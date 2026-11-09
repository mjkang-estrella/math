import NReplay022
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_34601 : CNF.NClause := [(44,false),(88,false),(13,true),(72,false),(78,false),(84,false)]
theorem der_34601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34601 :=
  CNF.rup_sound cl_34601 [cl_29409,cl_29244] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29409 v h) (hints_cons _ _ _ (der_29244 v h) (by intro d hd; cases hd)))
def cl_34602 : CNF.NClause := [(44,false),(84,false),(72,false),(88,false),(78,false),(71,true)]
theorem der_34602 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34602 :=
  CNF.rup_sound cl_34602 [cl_29410,cl_34499] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29410 v h) (hints_cons _ _ _ (der_34499 v h) (by intro d hd; cases hd)))
def cl_34603 : CNF.NClause := [(44,false),(78,false),(71,true),(13,false),(88,false),(84,false)]
theorem der_34603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34603 :=
  CNF.rup_sound cl_34603 [cl_29411,cl_34501] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29411 v h) (hints_cons _ _ _ (der_34501 v h) (by intro d hd; cases hd)))
def cl_34604 : CNF.NClause := [(44,false),(71,true),(13,false),(72,true),(88,false),(84,false)]
theorem der_34604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34604 :=
  CNF.rup_sound cl_34604 [cl_29413,cl_34603] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29413 v h) (hints_cons _ _ _ (der_34603 v h) (by intro d hd; cases hd)))
def cl_34605 : CNF.NClause := [(44,false),(13,false),(72,true),(71,true),(88,false),(78,false)]
theorem der_34605 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34605 :=
  CNF.rup_sound cl_34605 [cl_29415,cl_34603] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29415 v h) (hints_cons _ _ _ (der_34603 v h) (by intro d hd; cases hd)))
def cl_34606 : CNF.NClause := [(44,false),(78,true),(13,false),(72,false),(88,false),(65,false)]
theorem der_34606 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34606 :=
  CNF.rup_sound cl_34606 [cl_29416,cl_29412] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29416 v h) (hints_cons _ _ _ (der_29412 v h) (by intro d hd; cases hd)))
def cl_34608 : CNF.NClause := [(44,false),(78,false),(13,false),(72,false),(71,true),(84,false)]
theorem der_34608 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34608 :=
  CNF.rup_sound cl_34608 [cl_29418,cl_34603] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29418 v h) (hints_cons _ _ _ (der_34603 v h) (by intro d hd; cases hd)))
def cl_34609 : CNF.NClause := [(44,false),(78,false),(13,false),(72,true),(71,true),(84,false)]
theorem der_34609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34609 :=
  CNF.rup_sound cl_34609 [cl_29419,cl_34603] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29419 v h) (hints_cons _ _ _ (der_34603 v h) (by intro d hd; cases hd)))
def cl_34610 : CNF.NClause := [(44,false),(78,true),(13,false),(72,false),(84,false),(65,false)]
theorem der_34610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34610 :=
  CNF.rup_sound cl_34610 [cl_29420,cl_29412] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29420 v h) (hints_cons _ _ _ (der_29412 v h) (by intro d hd; cases hd)))
def cl_34611 : CNF.NClause := [(44,false),(78,true),(71,true),(13,false),(72,true),(84,false)]
theorem der_34611 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34611 :=
  CNF.rup_sound cl_34611 [cl_29421,cl_34604] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29421 v h) (hints_cons _ _ _ (der_34604 v h) (by intro d hd; cases hd)))
def cl_34612 : CNF.NClause := [(44,false),(84,true),(13,false),(72,false),(78,false),(65,false)]
theorem der_34612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34612 :=
  CNF.rup_sound cl_34612 [cl_29422,cl_29414] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29422 v h) (hints_cons _ _ _ (der_29414 v h) (by intro d hd; cases hd)))
def cl_34613 : CNF.NClause := [(44,false),(84,true),(13,false),(72,true),(71,true),(78,false)]
theorem der_34613 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34613 :=
  CNF.rup_sound cl_34613 [cl_29423,cl_34605] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29423 v h) (hints_cons _ _ _ (der_34605 v h) (by intro d hd; cases hd)))
def cl_34614 : CNF.NClause := [(44,false),(78,true),(13,false),(72,true),(84,true),(71,true)]
theorem der_34614 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34614 :=
  CNF.rup_sound cl_34614 [cl_29425,cl_34529] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29425 v h) (hints_cons _ _ _ (der_34529 v h) (by intro d hd; cases hd)))
def cl_34615 : CNF.NClause := [(44,false),(88,false),(71,true),(13,true),(78,false),(84,false)]
theorem der_34615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34615 :=
  CNF.rup_sound cl_34615 [cl_29426,cl_34602] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29426 v h) (hints_cons _ _ _ (der_34602 v h) (by intro d hd; cases hd)))
def cl_34616 : CNF.NClause := [(44,false),(84,false),(78,true),(72,false),(88,false),(65,false)]
theorem der_34616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34616 :=
  CNF.rup_sound cl_34616 [cl_29427,cl_29412] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29427 v h) (hints_cons _ _ _ (der_29412 v h) (by intro d hd; cases hd)))
def cl_34617 : CNF.NClause := [(44,false),(88,false),(71,true),(78,true),(72,true),(84,false)]
theorem der_34617 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34617 :=
  CNF.rup_sound cl_34617 [cl_29428,cl_34604] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29428 v h) (hints_cons _ _ _ (der_34604 v h) (by intro d hd; cases hd)))
def cl_34618 : CNF.NClause := [(44,false),(84,true),(72,false),(88,false),(78,false),(13,true)]
theorem der_34618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34618 :=
  CNF.rup_sound cl_34618 [cl_29429,cl_34457] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29429 v h) (hints_cons _ _ _ (der_34457 v h) (by intro d hd; cases hd)))
def cl_34619 : CNF.NClause := [(44,false),(84,true),(71,true),(72,true),(88,false),(78,false)]
theorem der_34619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34619 :=
  CNF.rup_sound cl_34619 [cl_29430,cl_34605] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29430 v h) (hints_cons _ _ _ (der_34605 v h) (by intro d hd; cases hd)))
def cl_34620 : CNF.NClause := [(44,false),(88,false),(78,true),(84,true),(72,false),(13,true)]
theorem der_34620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34620 :=
  CNF.rup_sound cl_34620 [cl_29431,cl_34475] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29431 v h) (hints_cons _ _ _ (der_34475 v h) (by intro d hd; cases hd)))
def cl_34621 : CNF.NClause := [(44,false),(71,true),(88,false),(78,true),(72,true),(13,true)]
theorem der_34621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34621 :=
  CNF.rup_sound cl_34621 [cl_29432,cl_34617] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29432 v h) (hints_cons _ _ _ (der_34617 v h) (by intro d hd; cases hd)))
def cl_34622 : CNF.NClause := [(44,false),(78,false),(71,true),(72,false),(84,false),(88,true)]
theorem der_34622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34622 :=
  CNF.rup_sound cl_34622 [cl_29433,cl_34608] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29433 v h) (hints_cons _ _ _ (der_34608 v h) (by intro d hd; cases hd)))
def cl_34623 : CNF.NClause := [(44,false),(78,false),(71,true),(72,true),(84,false),(88,true)]
theorem der_34623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34623 :=
  CNF.rup_sound cl_34623 [cl_29434,cl_34609] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29434 v h) (hints_cons _ _ _ (der_34609 v h) (by intro d hd; cases hd)))
def cl_34624 : CNF.NClause := [(44,false),(78,true),(13,true),(72,false),(84,false),(88,true)]
theorem der_34624 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34624 :=
  CNF.rup_sound cl_34624 [cl_29435,cl_34467] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29435 v h) (hints_cons _ _ _ (der_34467 v h) (by intro d hd; cases hd)))
def cl_34625 : CNF.NClause := [(44,false),(78,true),(71,true),(72,true),(84,false),(88,true)]
theorem der_34625 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34625 :=
  CNF.rup_sound cl_34625 [cl_29436,cl_34611] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29436 v h) (hints_cons _ _ _ (der_34611 v h) (by intro d hd; cases hd)))
def cl_34626 : CNF.NClause := [(44,false),(84,true),(13,true),(72,false),(78,false),(88,true)]
theorem der_34626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34626 :=
  CNF.rup_sound cl_34626 [cl_29437,cl_34471] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29437 v h) (hints_cons _ _ _ (der_34471 v h) (by intro d hd; cases hd)))
def cl_34627 : CNF.NClause := [(44,false),(84,true),(71,true),(72,true),(78,false),(65,false)]
theorem der_34627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34627 :=
  CNF.rup_sound cl_34627 [cl_29438,cl_34613] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29438 v h) (hints_cons _ _ _ (der_34613 v h) (by intro d hd; cases hd)))
def cl_34628 : CNF.NClause := [(44,false),(78,true),(71,true),(84,true),(72,false),(88,true)]
theorem der_34628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34628 :=
  CNF.rup_sound cl_34628 [cl_29439,cl_29424] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29439 v h) (hints_cons _ _ _ (der_29424 v h) (by intro d hd; cases hd)))
def cl_34629 : CNF.NClause := [(44,false),(78,true),(71,true),(13,true),(84,true),(88,true)]
theorem der_34629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34629 :=
  CNF.rup_sound cl_34629 [cl_29440,cl_34628] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29440 v h) (hints_cons _ _ _ (der_34628 v h) (by intro d hd; cases hd)))
def cl_34631 : CNF.NClause := [(44,false),(71,false),(72,false),(78,false),(13,true),(65,false)]
theorem der_34631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34631 :=
  CNF.rup_sound cl_34631 [cl_29442,cl_34300] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29442 v h) (hints_cons _ _ _ (der_34300 v h) (by intro d hd; cases hd)))
def cl_34632 : CNF.NClause := [(52,false),(85,false),(88,true),(67,false),(79,false),(21,true)]
theorem der_34632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34632 :=
  CNF.rup_sound cl_34632 [cl_29443,cl_34584] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29443 v h) (hints_cons _ _ _ (der_34584 v h) (by intro d hd; cases hd)))
def cl_34633 : CNF.NClause := [(61,false),(67,false),(77,false),(72,true),(62,false),(82,false)]
theorem der_34633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34633 :=
  CNF.rup_sound cl_34633 [cl_15589,cl_30920] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15589 v h) (hints_cons _ _ _ (der_30920 v h) (by intro d hd; cases hd)))
def cl_34634 : CNF.NClause := [(47,false),(77,false),(66,true),(16,true),(89,false),(84,false)]
theorem der_34634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34634 :=
  CNF.rup_sound cl_34634 [cl_29444,cl_34417] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29444 v h) (hints_cons _ _ _ (der_34417 v h) (by intro d hd; cases hd)))
def cl_34635 : CNF.NClause := [(47,false),(66,true),(77,true),(16,true),(89,false),(84,false)]
theorem der_34635 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34635 :=
  CNF.rup_sound cl_34635 [cl_29445,cl_34417] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29445 v h) (hints_cons _ _ _ (der_34417 v h) (by intro d hd; cases hd)))
def cl_34636 : CNF.NClause := [(47,false),(66,true),(84,true),(77,false),(89,false),(68,false)]
theorem der_34636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34636 :=
  CNF.rup_sound cl_34636 [cl_29446,cl_34418] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29446 v h) (hints_cons _ _ _ (der_34418 v h) (by intro d hd; cases hd)))
def cl_34637 : CNF.NClause := [(47,false),(75,true),(66,true),(84,true),(89,false),(68,false)]
theorem der_34637 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34637 :=
  CNF.rup_sound cl_34637 [cl_29447,cl_34636] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29447 v h) (hints_cons _ _ _ (der_34636 v h) (by intro d hd; cases hd)))
def cl_34638 : CNF.NClause := [(47,false),(84,false),(75,true),(66,true),(16,true),(77,false)]
theorem der_34638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34638 :=
  CNF.rup_sound cl_34638 [cl_29448,cl_34634] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29448 v h) (hints_cons _ _ _ (der_34634 v h) (by intro d hd; cases hd)))
def cl_34640 : CNF.NClause := [(47,false),(66,true),(84,true),(77,false),(68,false),(89,true)]
theorem der_34640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34640 :=
  CNF.rup_sound cl_34640 [cl_29450,cl_34422] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29450 v h) (hints_cons _ _ _ (der_34422 v h) (by intro d hd; cases hd)))
def cl_34641 : CNF.NClause := [(47,false),(66,true),(75,true),(77,true),(68,false),(89,true)]
theorem der_34641 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34641 :=
  CNF.rup_sound cl_34641 [cl_29451,cl_34405] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29451 v h) (hints_cons _ _ _ (der_34405 v h) (by intro d hd; cases hd)))
def cl_34642 : CNF.NClause := [(78,true),(53,false),(90,false),(67,false),(64,false),(86,false)]
theorem der_34642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34642 :=
  CNF.rup_sound cl_34642 [cl_29453,cl_32406] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29453 v h) (hints_cons _ _ _ (der_32406 v h) (by intro d hd; cases hd)))
def cl_34643 : CNF.NClause := [(53,false),(86,true),(90,false),(67,false),(64,false),(78,false)]
theorem der_34643 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34643 :=
  CNF.rup_sound cl_34643 [cl_29454,cl_32407] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29454 v h) (hints_cons _ _ _ (der_32407 v h) (by intro d hd; cases hd)))
def cl_34644 : CNF.NClause := [(78,true),(53,false),(86,true),(90,false),(67,false),(64,false)]
theorem der_34644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34644 :=
  CNF.rup_sound cl_34644 [cl_29455,cl_34313] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29455 v h) (hints_cons _ _ _ (der_34313 v h) (by intro d hd; cases hd)))
def cl_34645 : CNF.NClause := [(86,false),(53,false),(67,false),(64,false),(78,false),(90,true)]
theorem der_34645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34645 :=
  CNF.rup_sound cl_34645 [cl_29456,cl_32410] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29456 v h) (hints_cons _ _ _ (der_32410 v h) (by intro d hd; cases hd)))
def cl_34646 : CNF.NClause := [(78,true),(86,false),(67,false),(64,false),(53,false),(90,true)]
theorem der_34646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34646 :=
  CNF.rup_sound cl_34646 [cl_29457,cl_34314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29457 v h) (hints_cons _ _ _ (der_34314 v h) (by intro d hd; cases hd)))
def cl_34647 : CNF.NClause := [(53,false),(67,false),(86,true),(22,false),(64,false),(78,false)]
theorem der_34647 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34647 :=
  CNF.rup_sound cl_34647 [cl_29458,cl_34643] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29458 v h) (hints_cons _ _ _ (der_34643 v h) (by intro d hd; cases hd)))
def cl_34648 : CNF.NClause := [(78,true),(53,false),(86,true),(22,false),(67,false),(64,false)]
theorem der_34648 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34648 :=
  CNF.rup_sound cl_34648 [cl_29459,cl_34644] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29459 v h) (hints_cons _ _ _ (der_34644 v h) (by intro d hd; cases hd)))
def cl_34649 : CNF.NClause := [(47,false),(77,true),(16,false),(89,false),(84,false),(68,false)]
theorem der_34649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34649 :=
  CNF.rup_sound cl_34649 [cl_29461,cl_29161] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29461 v h) (hints_cons _ _ _ (der_29161 v h) (by intro d hd; cases hd)))
def cl_34650 : CNF.NClause := [(47,false),(84,true),(77,false),(16,false),(89,false),(68,false)]
theorem der_34650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34650 :=
  CNF.rup_sound cl_34650 [cl_29462,cl_34387] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29462 v h) (hints_cons _ _ _ (der_34387 v h) (by intro d hd; cases hd)))
def cl_34653 : CNF.NClause := [(47,false),(75,true),(77,true),(16,false),(84,false),(68,false)]
theorem der_34653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34653 :=
  CNF.rup_sound cl_34653 [cl_29465,cl_34649] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29465 v h) (hints_cons _ _ _ (der_34649 v h) (by intro d hd; cases hd)))
def cl_34655 : CNF.NClause := [(47,false),(84,true),(77,true),(16,false),(66,false),(89,true)]
theorem der_34655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34655 :=
  CNF.rup_sound cl_34655 [cl_29467,cl_34365] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29467 v h) (hints_cons _ _ _ (der_34365 v h) (by intro d hd; cases hd)))
def cl_34656 : CNF.NClause := [(86,false),(53,false),(78,true),(90,false),(22,true),(67,false)]
theorem der_34656 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34656 :=
  CNF.rup_sound cl_34656 [cl_29469,cl_34642] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29469 v h) (hints_cons _ _ _ (der_34642 v h) (by intro d hd; cases hd)))
def cl_34657 : CNF.NClause := [(78,false),(53,false),(86,true),(90,false),(22,true),(67,false)]
theorem der_34657 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34657 :=
  CNF.rup_sound cl_34657 [cl_29470,cl_34643] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29470 v h) (hints_cons _ _ _ (der_34643 v h) (by intro d hd; cases hd)))
def cl_34658 : CNF.NClause := [(90,false),(53,false),(78,true),(86,true),(22,true),(67,false)]
theorem der_34658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34658 :=
  CNF.rup_sound cl_34658 [cl_29471,cl_34318] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29471 v h) (hints_cons _ _ _ (der_34318 v h) (by intro d hd; cases hd)))
def cl_34659 : CNF.NClause := [(86,false),(53,false),(67,false),(78,false),(22,true),(90,true)]
theorem der_34659 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34659 :=
  CNF.rup_sound cl_34659 [cl_29472,cl_29040] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29472 v h) (hints_cons _ _ _ (der_29040 v h) (by intro d hd; cases hd)))
def cl_34660 : CNF.NClause := [(86,false),(53,false),(78,true),(67,false),(22,true),(90,true)]
theorem der_34660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34660 :=
  CNF.rup_sound cl_34660 [cl_29473,cl_34319] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29473 v h) (hints_cons _ _ _ (der_34319 v h) (by intro d hd; cases hd)))
def cl_34661 : CNF.NClause := [(53,false),(22,true),(86,true),(67,false),(78,false),(90,true)]
theorem der_34661 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34661 :=
  CNF.rup_sound cl_34661 [cl_29474,cl_32414] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29474 v h) (hints_cons _ _ _ (der_32414 v h) (by intro d hd; cases hd)))
def cl_34662 : CNF.NClause := [(47,false),(16,true),(77,false),(89,false),(66,false),(84,false)]
theorem der_34662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34662 :=
  CNF.rup_sound cl_34662 [cl_29476,cl_26364] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29476 v h) (hints_cons _ _ _ (der_26364 v h) (by intro d hd; cases hd)))
def cl_34663 : CNF.NClause := [(47,false),(77,true),(89,false),(66,false),(84,false),(68,false)]
theorem der_34663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34663 :=
  CNF.rup_sound cl_34663 [cl_29477,cl_26763] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29477 v h) (hints_cons _ _ _ (der_26763 v h) (by intro d hd; cases hd)))
def cl_34664 : CNF.NClause := [(47,false),(89,false),(84,true),(77,false),(16,true),(66,false)]
theorem der_34664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34664 :=
  CNF.rup_sound cl_34664 [cl_29478,cl_32027] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29478 v h) (hints_cons _ _ _ (der_32027 v h) (by intro d hd; cases hd)))
def cl_34665 : CNF.NClause := [(47,false),(75,true),(77,true),(84,true),(89,false),(68,false)]
theorem der_34665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34665 :=
  CNF.rup_sound cl_34665 [cl_29479,cl_34637] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29479 v h) (hints_cons _ _ _ (der_34637 v h) (by intro d hd; cases hd)))
def cl_34666 : CNF.NClause := [(47,false),(77,false),(66,false),(84,false),(68,false),(89,true)]
theorem der_34666 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34666 :=
  CNF.rup_sound cl_34666 [cl_29480,cl_34597] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29480 v h) (hints_cons _ _ _ (der_34597 v h) (by intro d hd; cases hd)))
def cl_34667 : CNF.NClause := [(47,false),(89,true),(75,true),(77,true),(84,false),(68,false)]
theorem der_34667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34667 :=
  CNF.rup_sound cl_34667 [cl_29481,cl_34653] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29481 v h) (hints_cons _ _ _ (der_34653 v h) (by intro d hd; cases hd)))
def cl_34668 : CNF.NClause := [(47,false),(84,true),(77,false),(66,false),(68,false),(89,true)]
theorem der_34668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34668 :=
  CNF.rup_sound cl_34668 [cl_29482,cl_34301] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29482 v h) (hints_cons _ _ _ (der_34301 v h) (by intro d hd; cases hd)))
def cl_34669 : CNF.NClause := [(47,false),(89,true),(77,true),(84,true),(66,false),(68,false)]
theorem der_34669 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34669 :=
  CNF.rup_sound cl_34669 [cl_29483,cl_34655] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29483 v h) (hints_cons _ _ _ (der_34655 v h) (by intro d hd; cases hd)))
def cl_34670 : CNF.NClause := [(45,false),(79,true),(86,true),(63,false),(89,false),(14,false)]
theorem der_34670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34670 :=
  CNF.rup_sound cl_34670 [cl_29487,cl_34327] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29487 v h) (hints_cons _ _ _ (der_34327 v h) (by intro d hd; cases hd)))
def cl_34671 : CNF.NClause := [(45,false),(72,true),(63,false),(79,false),(86,false),(14,false)]
theorem der_34671 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34671 :=
  CNF.rup_sound cl_34671 [cl_29488,cl_29484] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29488 v h) (hints_cons _ _ _ (der_29484 v h) (by intro d hd; cases hd)))
def cl_34672 : CNF.NClause := [(45,false),(79,true),(63,false),(86,false),(14,false),(89,true)]
theorem der_34672 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34672 :=
  CNF.rup_sound cl_34672 [cl_29489,cl_34330] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29489 v h) (hints_cons _ _ _ (der_34330 v h) (by intro d hd; cases hd)))
def cl_34673 : CNF.NClause := [(45,false),(72,true),(63,false),(79,false),(14,false),(89,true)]
theorem der_34673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34673 :=
  CNF.rup_sound cl_34673 [cl_29490,cl_34333] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29490 v h) (hints_cons _ _ _ (der_34333 v h) (by intro d hd; cases hd)))
def cl_34674 : CNF.NClause := [(45,false),(79,true),(86,true),(63,false),(14,false),(70,false)]
theorem der_34674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34674 :=
  CNF.rup_sound cl_34674 [cl_29491,cl_34670] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29491 v h) (hints_cons _ _ _ (der_34670 v h) (by intro d hd; cases hd)))
def cl_34675 : CNF.NClause := [(45,false),(86,true),(14,true),(63,true),(89,false),(79,false)]
theorem der_34675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34675 :=
  CNF.rup_sound cl_34675 [cl_29494,cl_34339] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29494 v h) (hints_cons _ _ _ (der_34339 v h) (by intro d hd; cases hd)))
def cl_34677 : CNF.NClause := [(44,false),(88,false),(13,false),(72,true),(78,false),(84,false)]
theorem der_34677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34677 :=
  CNF.rup_sound cl_34677 [cl_29496,cl_34603] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29496 v h) (hints_cons _ _ _ (der_34603 v h) (by intro d hd; cases hd)))
def cl_34678 : CNF.NClause := [(44,false),(78,true),(13,false),(72,true),(84,true),(88,false)]
theorem der_34678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34678 :=
  CNF.rup_sound cl_34678 [cl_29499,cl_34614] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29499 v h) (hints_cons _ _ _ (der_34614 v h) (by intro d hd; cases hd)))
def cl_34679 : CNF.NClause := [(44,false),(72,true),(78,false),(13,false),(84,false),(88,true)]
theorem der_34679 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34679 :=
  CNF.rup_sound cl_34679 [cl_29500,cl_34609] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29500 v h) (hints_cons _ _ _ (der_34609 v h) (by intro d hd; cases hd)))
def cl_34680 : CNF.NClause := [(44,false),(78,true),(13,false),(71,false),(84,false),(65,false)]
theorem der_34680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34680 :=
  CNF.rup_sound cl_34680 [cl_29501,cl_29497] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29501 v h) (hints_cons _ _ _ (der_29497 v h) (by intro d hd; cases hd)))
def cl_34681 : CNF.NClause := [(44,false),(71,false),(78,false),(13,false),(65,false),(88,true)]
theorem der_34681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34681 :=
  CNF.rup_sound cl_34681 [cl_29502,cl_29441] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29502 v h) (hints_cons _ _ _ (der_29441 v h) (by intro d hd; cases hd)))
def cl_34682 : CNF.NClause := [(44,false),(78,true),(13,false),(84,true),(71,false),(65,false)]
theorem der_34682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34682 :=
  CNF.rup_sound cl_34682 [cl_29503,cl_34317] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29503 v h) (hints_cons _ _ _ (der_34317 v h) (by intro d hd; cases hd)))
def cl_34683 : CNF.NClause := [(45,false),(89,false),(14,true),(63,false),(79,false),(86,false)]
theorem der_34683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34683 :=
  CNF.rup_sound cl_34683 [cl_29504,cl_26810] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29504 v h) (hints_cons _ _ _ (der_26810 v h) (by intro d hd; cases hd)))
def cl_34684 : CNF.NClause := [(45,false),(70,false),(79,true),(89,false),(86,false),(14,true)]
theorem der_34684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34684 :=
  CNF.rup_sound cl_34684 [cl_29505,cl_29493] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29505 v h) (hints_cons _ _ _ (der_29493 v h) (by intro d hd; cases hd)))
def cl_34685 : CNF.NClause := [(45,false),(79,false),(86,true),(63,false),(89,false),(70,false)]
theorem der_34685 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34685 :=
  CNF.rup_sound cl_34685 [cl_29506,cl_29486] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29506 v h) (hints_cons _ _ _ (der_29486 v h) (by intro d hd; cases hd)))
def cl_34686 : CNF.NClause := [(45,false),(70,false),(79,true),(72,true),(89,false),(14,true)]
theorem der_34686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34686 :=
  CNF.rup_sound cl_34686 [cl_29507,cl_34684] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29507 v h) (hints_cons _ _ _ (der_34684 v h) (by intro d hd; cases hd)))
def cl_34687 : CNF.NClause := [(45,false),(79,false),(14,true),(63,false),(86,false),(70,false)]
theorem der_34687 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34687 :=
  CNF.rup_sound cl_34687 [cl_29508,cl_34683] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29508 v h) (hints_cons _ _ _ (der_34683 v h) (by intro d hd; cases hd)))
def cl_34688 : CNF.NClause := [(45,false),(79,true),(72,true),(63,false),(86,false),(14,true)]
theorem der_34688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34688 :=
  CNF.rup_sound cl_34688 [cl_29509,cl_32443] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29509 v h) (hints_cons _ _ _ (der_32443 v h) (by intro d hd; cases hd)))
def cl_34689 : CNF.NClause := [(45,false),(63,false),(86,true),(79,false),(70,false),(89,true)]
theorem der_34689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34689 :=
  CNF.rup_sound cl_34689 [cl_29510,cl_34293] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29510 v h) (hints_cons _ _ _ (der_34293 v h) (by intro d hd; cases hd)))
def cl_34690 : CNF.NClause := [(45,false),(89,true),(86,true),(63,false),(70,false),(14,true)]
theorem der_34690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34690 :=
  CNF.rup_sound cl_34690 [cl_29511,cl_34689] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29511 v h) (hints_cons _ _ _ (der_34689 v h) (by intro d hd; cases hd)))
def cl_34691 : CNF.NClause := [(44,false),(78,false),(13,true),(88,false),(71,false),(84,false)]
theorem der_34691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34691 :=
  CNF.rup_sound cl_34691 [cl_29512,cl_29246] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29512 v h) (hints_cons _ _ _ (der_29246 v h) (by intro d hd; cases hd)))
def cl_34692 : CNF.NClause := [(44,false),(71,false),(13,true),(88,false),(84,false),(65,false)]
theorem der_34692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34692 :=
  CNF.rup_sound cl_34692 [cl_29513,cl_34691] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29513 v h) (hints_cons _ _ _ (der_34691 v h) (by intro d hd; cases hd)))
def cl_34693 : CNF.NClause := [(44,false),(78,false),(88,false),(13,true),(71,false),(65,false)]
theorem der_34693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34693 :=
  CNF.rup_sound cl_34693 [cl_29514,cl_34691] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29514 v h) (hints_cons _ _ _ (der_34691 v h) (by intro d hd; cases hd)))
def cl_34694 : CNF.NClause := [(44,false),(71,false),(78,true),(72,true),(84,true),(88,false)]
theorem der_34694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34694 :=
  CNF.rup_sound cl_34694 [cl_29515,cl_34678] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29515 v h) (hints_cons _ _ _ (der_34678 v h) (by intro d hd; cases hd)))
def cl_34695 : CNF.NClause := [(44,false),(71,false),(72,true),(78,false),(13,true),(84,false)]
theorem der_34695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34695 :=
  CNF.rup_sound cl_34695 [cl_29516,cl_34473] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29516 v h) (hints_cons _ _ _ (der_34473 v h) (by intro d hd; cases hd)))
def cl_34696 : CNF.NClause := [(44,false),(71,false),(13,true),(72,true),(84,false),(65,false)]
theorem der_34696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34696 :=
  CNF.rup_sound cl_34696 [cl_29517,cl_34692] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29517 v h) (hints_cons _ _ _ (der_34692 v h) (by intro d hd; cases hd)))
def cl_34697 : CNF.NClause := [(44,false),(71,false),(72,true),(78,false),(13,true),(88,true)]
theorem der_34697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34697 :=
  CNF.rup_sound cl_34697 [cl_29518,cl_34473] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29518 v h) (hints_cons _ _ _ (der_34473 v h) (by intro d hd; cases hd)))
def cl_34698 : CNF.NClause := [(44,false),(78,true),(13,true),(71,false),(65,false),(88,true)]
theorem der_34698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34698 :=
  CNF.rup_sound cl_34698 [cl_29519,cl_32381] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29519 v h) (hints_cons _ _ _ (der_32381 v h) (by intro d hd; cases hd)))
def cl_34699 : CNF.NClause := [(49,false),(73,true),(77,false),(91,false),(86,false),(18,false)]
theorem der_34699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34699 :=
  CNF.rup_sound cl_34699 [cl_29521,cl_29371] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29521 v h) (hints_cons _ _ _ (der_29371 v h) (by intro d hd; cases hd)))
def cl_34700 : CNF.NClause := [(49,false),(77,true),(91,false),(86,false),(73,false),(18,false)]
theorem der_34700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34700 :=
  CNF.rup_sound cl_34700 [cl_29522,cl_34488] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29522 v h) (hints_cons _ _ _ (der_34488 v h) (by intro d hd; cases hd)))
def cl_34701 : CNF.NClause := [(49,false),(73,true),(69,true),(91,false),(86,false),(18,false)]
theorem der_34701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34701 :=
  CNF.rup_sound cl_34701 [cl_29523,cl_34699] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29523 v h) (hints_cons _ _ _ (der_34699 v h) (by intro d hd; cases hd)))
def cl_34702 : CNF.NClause := [(49,false),(86,true),(77,false),(91,false),(73,false),(18,false)]
theorem der_34702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34702 :=
  CNF.rup_sound cl_34702 [cl_29524,cl_29283] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29524 v h) (hints_cons _ _ _ (der_29283 v h) (by intro d hd; cases hd)))
def cl_34703 : CNF.NClause := [(49,false),(77,false),(69,true),(73,true),(91,false),(18,false)]
theorem der_34703 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34703 :=
  CNF.rup_sound cl_34703 [cl_29525,cl_34701] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29525 v h) (hints_cons _ _ _ (der_34701 v h) (by intro d hd; cases hd)))
def cl_34705 : CNF.NClause := [(49,false),(73,true),(69,true),(77,true),(91,false),(18,false)]
theorem der_34705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34705 :=
  CNF.rup_sound cl_34705 [cl_29527,cl_34701] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29527 v h) (hints_cons _ _ _ (der_34701 v h) (by intro d hd; cases hd)))
def cl_34707 : CNF.NClause := [(49,false),(77,true),(86,false),(73,false),(18,false),(91,true)]
theorem der_34707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34707 :=
  CNF.rup_sound cl_34707 [cl_29530,cl_34488] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29530 v h) (hints_cons _ _ _ (der_34488 v h) (by intro d hd; cases hd)))
def cl_34708 : CNF.NClause := [(49,false),(86,false),(69,true),(77,true),(73,true),(18,false)]
theorem der_34708 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34708 :=
  CNF.rup_sound cl_34708 [cl_29531,cl_34701] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29531 v h) (hints_cons _ _ _ (der_34701 v h) (by intro d hd; cases hd)))
def cl_34709 : CNF.NClause := [(49,false),(86,true),(77,false),(73,false),(18,false),(91,true)]
theorem der_34709 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34709 :=
  CNF.rup_sound cl_34709 [cl_29532,cl_34492] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29532 v h) (hints_cons _ _ _ (der_34492 v h) (by intro d hd; cases hd)))
def cl_34711 : CNF.NClause := [(49,false),(77,true),(73,false),(18,false),(86,true),(91,true)]
theorem der_34711 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34711 :=
  CNF.rup_sound cl_34711 [cl_29534,cl_34497] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29534 v h) (hints_cons _ _ _ (der_34497 v h) (by intro d hd; cases hd)))
def cl_34712 : CNF.NClause := [(49,false),(69,true),(86,true),(77,true),(18,false),(91,true)]
theorem der_34712 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34712 :=
  CNF.rup_sound cl_34712 [cl_29535,cl_34711] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29535 v h) (hints_cons _ _ _ (der_34711 v h) (by intro d hd; cases hd)))
def cl_34713 : CNF.NClause := [(49,false),(77,false),(18,true),(91,false),(86,false),(73,false)]
theorem der_34713 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34713 :=
  CNF.rup_sound cl_34713 [cl_29536,cl_34530] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29536 v h) (hints_cons _ _ _ (der_34530 v h) (by intro d hd; cases hd)))
def cl_34714 : CNF.NClause := [(49,false),(77,false),(73,true),(69,true),(91,false),(86,false)]
theorem der_34714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34714 :=
  CNF.rup_sound cl_34714 [cl_29537,cl_34701] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29537 v h) (hints_cons _ _ _ (der_34701 v h) (by intro d hd; cases hd)))
def cl_34715 : CNF.NClause := [(49,false),(73,false),(77,true),(91,false),(86,false),(65,false)]
theorem der_34715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34715 :=
  CNF.rup_sound cl_34715 [cl_29538,cl_34700] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29538 v h) (hints_cons _ _ _ (der_34700 v h) (by intro d hd; cases hd)))
def cl_34716 : CNF.NClause := [(49,false),(69,true),(77,true),(91,false),(86,false),(65,false)]
theorem der_34716 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34716 :=
  CNF.rup_sound cl_34716 [cl_29539,cl_34715] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29539 v h) (hints_cons _ _ _ (der_34715 v h) (by intro d hd; cases hd)))
def cl_34717 : CNF.NClause := [(49,false),(73,false),(69,true),(86,true),(77,false),(91,false)]
theorem der_34717 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34717 :=
  CNF.rup_sound cl_34717 [cl_29540,cl_34702] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29540 v h) (hints_cons _ _ _ (der_34702 v h) (by intro d hd; cases hd)))
def cl_34718 : CNF.NClause := [(49,false),(77,false),(73,true),(69,true),(86,true),(91,false)]
theorem der_34718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34718 :=
  CNF.rup_sound cl_34718 [cl_29541,cl_34703] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29541 v h) (hints_cons _ _ _ (der_34703 v h) (by intro d hd; cases hd)))
def cl_34719 : CNF.NClause := [(49,false),(73,false),(77,true),(91,false),(18,true),(65,false)]
theorem der_34719 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34719 :=
  CNF.rup_sound cl_34719 [cl_29542,cl_34715] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29542 v h) (hints_cons _ _ _ (der_34715 v h) (by intro d hd; cases hd)))
def cl_34720 : CNF.NClause := [(49,false),(91,false),(73,true),(86,true),(18,true),(77,true)]
theorem der_34720 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34720 :=
  CNF.rup_sound cl_34720 [cl_29543,cl_34544] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29543 v h) (hints_cons _ _ _ (der_34544 v h) (by intro d hd; cases hd)))
def cl_34721 : CNF.NClause := [(49,false),(86,false),(18,true),(77,false),(73,false),(65,false)]
theorem der_34721 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34721 :=
  CNF.rup_sound cl_34721 [cl_29544,cl_34713] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29544 v h) (hints_cons _ _ _ (der_34713 v h) (by intro d hd; cases hd)))
def cl_34722 : CNF.NClause := [(49,false),(86,false),(77,false),(18,true),(65,false),(91,true)]
theorem der_34722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34722 :=
  CNF.rup_sound cl_34722 [cl_29545,cl_34721] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29545 v h) (hints_cons _ _ _ (der_34721 v h) (by intro d hd; cases hd)))
def cl_34723 : CNF.NClause := [(49,false),(73,false),(69,true),(77,true),(86,false),(91,true)]
theorem der_34723 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34723 :=
  CNF.rup_sound cl_34723 [cl_29546,cl_34707] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29546 v h) (hints_cons _ _ _ (der_34707 v h) (by intro d hd; cases hd)))
def cl_34724 : CNF.NClause := [(49,false),(86,false),(73,true),(18,true),(65,false),(91,true)]
theorem der_34724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34724 :=
  CNF.rup_sound cl_34724 [cl_29547,cl_34722] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29547 v h) (hints_cons _ _ _ (der_34722 v h) (by intro d hd; cases hd)))
def cl_34725 : CNF.NClause := [(49,false),(91,true),(86,true),(77,false),(73,false),(65,false)]
theorem der_34725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34725 :=
  CNF.rup_sound cl_34725 [cl_29548,cl_34709] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29548 v h) (hints_cons _ _ _ (der_34709 v h) (by intro d hd; cases hd)))
def cl_34726 : CNF.NClause := [(49,false),(77,false),(69,true),(86,true),(73,true),(65,false)]
theorem der_34726 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34726 :=
  CNF.rup_sound cl_34726 [cl_29549,cl_34718] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29549 v h) (hints_cons _ _ _ (der_34718 v h) (by intro d hd; cases hd)))
def cl_34727 : CNF.NClause := [(49,false),(65,false),(86,true),(77,true),(73,false),(91,true)]
theorem der_34727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34727 :=
  CNF.rup_sound cl_34727 [cl_29550,cl_34711] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29550 v h) (hints_cons _ _ _ (der_34711 v h) (by intro d hd; cases hd)))
def cl_34728 : CNF.NClause := [(49,false),(77,true),(73,true),(69,true),(86,true),(91,true)]
theorem der_34728 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34728 :=
  CNF.rup_sound cl_34728 [cl_29551,cl_34712] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29551 v h) (hints_cons _ _ _ (der_34712 v h) (by intro d hd; cases hd)))
def cl_34729 : CNF.NClause := [(52,false),(88,false),(85,false),(66,true),(79,false),(73,false)]
theorem der_34729 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34729 :=
  CNF.rup_sound cl_34729 [cl_29552,cl_29212] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29552 v h) (hints_cons _ _ _ (der_29212 v h) (by intro d hd; cases hd)))
def cl_34730 : CNF.NClause := [(52,false),(85,false),(66,true),(88,false),(79,false),(21,false)]
theorem der_34730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34730 :=
  CNF.rup_sound cl_34730 [cl_29553,cl_34729] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29553 v h) (hints_cons _ _ _ (der_34729 v h) (by intro d hd; cases hd)))
def cl_34731 : CNF.NClause := [(52,false),(67,true),(85,false),(88,false),(73,false),(66,true)]
theorem der_34731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34731 :=
  CNF.rup_sound cl_34731 [cl_29554,cl_34427] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29554 v h) (hints_cons _ _ _ (der_34427 v h) (by intro d hd; cases hd)))
def cl_34732 : CNF.NClause := [(52,false),(73,true),(66,true),(85,false),(88,false),(21,false)]
theorem der_34732 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34732 :=
  CNF.rup_sound cl_34732 [cl_29555,cl_34730] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29555 v h) (hints_cons _ _ _ (der_34730 v h) (by intro d hd; cases hd)))
def cl_34733 : CNF.NClause := [(52,false),(66,true),(88,false),(79,false),(73,false),(85,true)]
theorem der_34733 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34733 :=
  CNF.rup_sound cl_34733 [cl_29556,cl_34430] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29556 v h) (hints_cons _ _ _ (der_34430 v h) (by intro d hd; cases hd)))
def cl_34734 : CNF.NClause := [(52,false),(66,true),(88,false),(79,false),(85,true),(21,false)]
theorem der_34734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34734 :=
  CNF.rup_sound cl_34734 [cl_29557,cl_34733] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29557 v h) (hints_cons _ _ _ (der_34733 v h) (by intro d hd; cases hd)))
def cl_34737 : CNF.NClause := [(52,false),(66,true),(85,false),(79,false),(73,false),(21,false)]
theorem der_34737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34737 :=
  CNF.rup_sound cl_34737 [cl_29560,cl_34729] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29560 v h) (hints_cons _ _ _ (der_34729 v h) (by intro d hd; cases hd)))
def cl_34738 : CNF.NClause := [(52,false),(66,true),(85,false),(79,false),(21,false),(88,true)]
theorem der_34738 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34738 :=
  CNF.rup_sound cl_34738 [cl_29561,cl_34737] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29561 v h) (hints_cons _ _ _ (der_34737 v h) (by intro d hd; cases hd)))
def cl_34740 : CNF.NClause := [(52,false),(73,true),(66,true),(85,false),(21,false),(88,true)]
theorem der_34740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34740 :=
  CNF.rup_sound cl_34740 [cl_29563,cl_34738] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29563 v h) (hints_cons _ _ _ (der_34738 v h) (by intro d hd; cases hd)))
def cl_34741 : CNF.NClause := [(52,false),(73,false),(79,false),(66,true),(67,true),(21,false)]
theorem der_34741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34741 :=
  CNF.rup_sound cl_34741 [cl_29564,cl_34737] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29564 v h) (hints_cons _ _ _ (der_34737 v h) (by intro d hd; cases hd)))
def cl_34742 : CNF.NClause := [(52,false),(73,true),(66,true),(79,false),(21,false),(88,true)]
theorem der_34742 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34742 :=
  CNF.rup_sound cl_34742 [cl_29565,cl_34738] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29565 v h) (hints_cons _ _ _ (der_34738 v h) (by intro d hd; cases hd)))
def cl_34745 : CNF.NClause := [(53,false),(75,true),(22,false),(90,false),(64,false),(86,false)]
theorem der_34745 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34745 :=
  CNF.rup_sound cl_34745 [cl_29570,cl_29568] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29570 v h) (hints_cons _ _ _ (der_29568 v h) (by intro d hd; cases hd)))
def cl_34746 : CNF.NClause := [(90,false),(53,false),(75,true),(22,false),(64,false),(78,false)]
theorem der_34746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34746 :=
  CNF.rup_sound cl_34746 [cl_29572,cl_29568] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29572 v h) (hints_cons _ _ _ (der_29568 v h) (by intro d hd; cases hd)))
def cl_34747 : CNF.NClause := [(78,true),(53,false),(22,false),(90,false),(64,false),(75,false)]
theorem der_34747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34747 :=
  CNF.rup_sound cl_34747 [cl_29573,cl_29569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29573 v h) (hints_cons _ _ _ (der_29569 v h) (by intro d hd; cases hd)))
def cl_34749 : CNF.NClause := [(75,true),(78,false),(22,false),(64,false),(53,false),(86,false)]
theorem der_34749 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34749 :=
  CNF.rup_sound cl_34749 [cl_29576,cl_29568] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29576 v h) (hints_cons _ _ _ (der_29568 v h) (by intro d hd; cases hd)))
def cl_34750 : CNF.NClause := [(78,true),(75,false),(22,false),(64,false),(86,false),(53,false)]
theorem der_34750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34750 :=
  CNF.rup_sound cl_34750 [cl_29577,cl_29569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29577 v h) (hints_cons _ _ _ (der_29569 v h) (by intro d hd; cases hd)))
def cl_34751 : CNF.NClause := [(78,true),(86,false),(75,true),(22,false),(64,false),(53,false)]
theorem der_34751 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34751 :=
  CNF.rup_sound cl_34751 [cl_29578,cl_34745] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29578 v h) (hints_cons _ _ _ (der_34745 v h) (by intro d hd; cases hd)))
def cl_34754 : CNF.NClause := [(78,true),(75,false),(86,true),(22,false),(64,false),(53,false)]
theorem der_34754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34754 :=
  CNF.rup_sound cl_34754 [cl_29581,cl_34747] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29581 v h) (hints_cons _ _ _ (der_34747 v h) (by intro d hd; cases hd)))
def cl_34756 : CNF.NClause := [(52,false),(85,false),(88,false),(79,false),(73,false),(67,true)]
theorem der_34756 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34756 :=
  CNF.rup_sound cl_34756 [cl_29583,cl_34731] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29583 v h) (hints_cons _ _ _ (der_34731 v h) (by intro d hd; cases hd)))
def cl_34757 : CNF.NClause := [(52,false),(73,true),(85,false),(88,false),(79,false),(21,false)]
theorem der_34757 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34757 :=
  CNF.rup_sound cl_34757 [cl_29584,cl_34730] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29584 v h) (hints_cons _ _ _ (der_34730 v h) (by intro d hd; cases hd)))
def cl_34758 : CNF.NClause := [(52,false),(73,false),(85,false),(88,false),(66,false),(79,true)]
theorem der_34758 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34758 :=
  CNF.rup_sound cl_34758 [cl_29585,cl_34308] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29585 v h) (hints_cons _ _ _ (der_34308 v h) (by intro d hd; cases hd)))
def cl_34759 : CNF.NClause := [(52,false),(73,true),(85,false),(88,false),(66,false),(67,true)]
theorem der_34759 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34759 :=
  CNF.rup_sound cl_34759 [cl_29586,cl_32094] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29586 v h) (hints_cons _ _ _ (der_32094 v h) (by intro d hd; cases hd)))
def cl_34760 : CNF.NClause := [(52,false),(88,false),(79,false),(73,false),(85,true),(21,false)]
theorem der_34760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34760 :=
  CNF.rup_sound cl_34760 [cl_29587,cl_34733] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29587 v h) (hints_cons _ _ _ (der_34733 v h) (by intro d hd; cases hd)))
def cl_34764 : CNF.NClause := [(52,false),(85,false),(79,false),(66,false),(73,false),(67,true)]
theorem der_34764 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34764 :=
  CNF.rup_sound cl_34764 [cl_29591,cl_34756] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29591 v h) (hints_cons _ _ _ (der_34756 v h) (by intro d hd; cases hd)))
def cl_34765 : CNF.NClause := [(52,false),(85,false),(79,false),(66,false),(67,true),(21,false)]
theorem der_34765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34765 :=
  CNF.rup_sound cl_34765 [cl_29592,cl_34764] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29592 v h) (hints_cons _ _ _ (der_34764 v h) (by intro d hd; cases hd)))
def cl_34766 : CNF.NClause := [(52,false),(85,false),(66,false),(73,false),(79,true),(21,false)]
theorem der_34766 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34766 :=
  CNF.rup_sound cl_34766 [cl_29593,cl_34758] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29593 v h) (hints_cons _ _ _ (der_34758 v h) (by intro d hd; cases hd)))
def cl_34768 : CNF.NClause := [(52,false),(79,false),(66,false),(73,false),(85,true),(21,false)]
theorem der_34768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34768 :=
  CNF.rup_sound cl_34768 [cl_29595,cl_34760] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29595 v h) (hints_cons _ _ _ (der_34760 v h) (by intro d hd; cases hd)))
def cl_34769 : CNF.NClause := [(52,false),(79,false),(66,false),(85,true),(21,false),(88,true)]
theorem der_34769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34769 :=
  CNF.rup_sound cl_34769 [cl_29596,cl_34768] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29596 v h) (hints_cons _ _ _ (der_34768 v h) (by intro d hd; cases hd)))
def cl_34772 : CNF.NClause := [(86,false),(90,false),(64,true),(75,true),(22,true),(53,false)]
theorem der_34772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34772 :=
  CNF.rup_sound cl_34772 [cl_29601,cl_29599] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29601 v h) (hints_cons _ _ _ (der_29599 v h) (by intro d hd; cases hd)))
def cl_34773 : CNF.NClause := [(78,false),(53,false),(86,true),(64,true),(90,false),(22,true)]
theorem der_34773 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34773 :=
  CNF.rup_sound cl_34773 [cl_29603,cl_29602] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29603 v h) (hints_cons _ _ _ (der_29602 v h) (by intro d hd; cases hd)))
def cl_34775 : CNF.NClause := [(75,true),(53,false),(86,true),(64,true),(22,true),(90,false)]
theorem der_34775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34775 :=
  CNF.rup_sound cl_34775 [cl_29605,cl_34773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29605 v h) (hints_cons _ _ _ (der_34773 v h) (by intro d hd; cases hd)))
def cl_34776 : CNF.NClause := [(78,false),(53,false),(22,true),(64,true),(86,false),(90,true)]
theorem der_34776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34776 :=
  CNF.rup_sound cl_34776 [cl_29607,cl_34659] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29607 v h) (hints_cons _ _ _ (der_34659 v h) (by intro d hd; cases hd)))
def cl_34778 : CNF.NClause := [(86,false),(53,false),(64,true),(75,true),(22,true),(90,true)]
theorem der_34778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34778 :=
  CNF.rup_sound cl_34778 [cl_29609,cl_34776] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29609 v h) (hints_cons _ _ _ (der_34776 v h) (by intro d hd; cases hd)))
def cl_34779 : CNF.NClause := [(90,true),(53,false),(64,true),(78,false),(75,false),(22,true)]
theorem der_34779 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34779 :=
  CNF.rup_sound cl_34779 [cl_29610,cl_34294] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29610 v h) (hints_cons _ _ _ (der_34294 v h) (by intro d hd; cases hd)))
def cl_34780 : CNF.NClause := [(53,false),(86,true),(64,true),(75,true),(78,false),(22,true)]
theorem der_34780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34780 :=
  CNF.rup_sound cl_34780 [cl_29611,cl_34773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29611 v h) (hints_cons _ _ _ (der_34773 v h) (by intro d hd; cases hd)))
def cl_34781 : CNF.NClause := [(75,true),(53,false),(78,true),(86,true),(64,true),(22,true)]
theorem der_34781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34781 :=
  CNF.rup_sound cl_34781 [cl_29613,cl_34775] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29613 v h) (hints_cons _ _ _ (der_34775 v h) (by intro d hd; cases hd)))
def cl_34782 : CNF.NClause := [(78,false),(53,false),(90,false),(22,true),(64,false),(86,false)]
theorem der_34782 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34782 :=
  CNF.rup_sound cl_34782 [cl_29615,cl_29614] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29615 v h) (hints_cons _ _ _ (der_29614 v h) (by intro d hd; cases hd)))
def cl_34783 : CNF.NClause := [(86,false),(53,false),(90,false),(64,false),(22,true),(75,false)]
theorem der_34783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34783 :=
  CNF.rup_sound cl_34783 [cl_29616,cl_29614] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29616 v h) (hints_cons _ _ _ (der_29614 v h) (by intro d hd; cases hd)))
def cl_34784 : CNF.NClause := [(78,true),(86,false),(75,true),(90,false),(64,false),(53,false)]
theorem der_34784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34784 :=
  CNF.rup_sound cl_34784 [cl_29617,cl_34642] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29617 v h) (hints_cons _ _ _ (der_34642 v h) (by intro d hd; cases hd)))
def cl_34785 : CNF.NClause := [(75,false),(53,false),(86,true),(90,false),(78,false),(22,true)]
theorem der_34785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34785 :=
  CNF.rup_sound cl_34785 [cl_29618,cl_29602] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29618 v h) (hints_cons _ _ _ (der_29602 v h) (by intro d hd; cases hd)))
def cl_34786 : CNF.NClause := [(53,false),(75,true),(90,false),(64,false),(78,false),(86,true)]
theorem der_34786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34786 :=
  CNF.rup_sound cl_34786 [cl_29619,cl_34643] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29619 v h) (hints_cons _ _ _ (der_34643 v h) (by intro d hd; cases hd)))
def cl_34787 : CNF.NClause := [(75,false),(53,false),(86,true),(90,false),(22,true),(67,true)]
theorem der_34787 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34787 :=
  CNF.rup_sound cl_34787 [cl_29620,cl_34785] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29620 v h) (hints_cons _ _ _ (der_34785 v h) (by intro d hd; cases hd)))
def cl_34788 : CNF.NClause := [(90,false),(53,false),(78,true),(86,true),(75,true),(22,true)]
theorem der_34788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34788 :=
  CNF.rup_sound cl_34788 [cl_29621,cl_34775] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29621 v h) (hints_cons _ _ _ (der_34775 v h) (by intro d hd; cases hd)))
def cl_34789 : CNF.NClause := [(78,false),(53,false),(22,true),(86,false),(75,false),(90,true)]
theorem der_34789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34789 :=
  CNF.rup_sound cl_34789 [cl_29622,cl_34776] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29622 v h) (hints_cons _ _ _ (der_34776 v h) (by intro d hd; cases hd)))
def cl_34790 : CNF.NClause := [(75,true),(86,false),(64,false),(78,false),(53,false),(90,true)]
theorem der_34790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34790 :=
  CNF.rup_sound cl_34790 [cl_29623,cl_34645] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29623 v h) (hints_cons _ _ _ (der_34645 v h) (by intro d hd; cases hd)))
def cl_34791 : CNF.NClause := [(90,true),(53,false),(86,false),(75,false),(22,true),(67,true)]
theorem der_34791 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34791 :=
  CNF.rup_sound cl_34791 [cl_29624,cl_34789] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29624 v h) (hints_cons _ _ _ (der_34789 v h) (by intro d hd; cases hd)))
def cl_34792 : CNF.NClause := [(86,false),(53,false),(78,true),(75,true),(64,false),(22,true)]
theorem der_34792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34792 :=
  CNF.rup_sound cl_34792 [cl_29625,cl_34784] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29625 v h) (hints_cons _ _ _ (der_34784 v h) (by intro d hd; cases hd)))
def cl_34793 : CNF.NClause := [(90,true),(53,false),(64,false),(78,false),(75,false),(86,true)]
theorem der_34793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34793 :=
  CNF.rup_sound cl_34793 [cl_29626,cl_34292] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29626 v h) (hints_cons _ _ _ (der_34292 v h) (by intro d hd; cases hd)))
def cl_34794 : CNF.NClause := [(90,true),(53,false),(64,false),(78,false),(67,true),(86,true)]
theorem der_34794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34794 :=
  CNF.rup_sound cl_34794 [cl_29627,cl_34793] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29627 v h) (hints_cons _ _ _ (der_34793 v h) (by intro d hd; cases hd)))
def cl_34795 : CNF.NClause := [(75,false),(53,false),(78,true),(86,true),(64,false),(90,true)]
theorem der_34795 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34795 :=
  CNF.rup_sound cl_34795 [cl_29628,cl_34754] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29628 v h) (hints_cons _ _ _ (der_34754 v h) (by intro d hd; cases hd)))
def cl_34796 : CNF.NClause := [(53,false),(86,true),(75,true),(64,false),(67,true),(90,true)]
theorem der_34796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34796 :=
  CNF.rup_sound cl_34796 [cl_29629,cl_34794] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29629 v h) (hints_cons _ _ _ (der_34794 v h) (by intro d hd; cases hd)))
def cl_34797 : CNF.NClause := [(45,false),(72,false),(70,true),(89,false),(79,false),(86,false)]
theorem der_34797 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34797 :=
  CNF.rup_sound cl_34797 [cl_29630,cl_34343] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29630 v h) (hints_cons _ _ _ (der_34343 v h) (by intro d hd; cases hd)))
def cl_34798 : CNF.NClause := [(45,false),(79,false),(89,false),(70,true),(86,false),(14,false)]
theorem der_34798 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34798 :=
  CNF.rup_sound cl_34798 [cl_29632,cl_34797] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29632 v h) (hints_cons _ _ _ (der_34797 v h) (by intro d hd; cases hd)))
def cl_34799 : CNF.NClause := [(45,false),(79,true),(72,false),(89,false),(86,false),(70,false)]
theorem der_34799 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34799 :=
  CNF.rup_sound cl_34799 [cl_29633,cl_34684] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29633 v h) (hints_cons _ _ _ (der_34684 v h) (by intro d hd; cases hd)))
def cl_34800 : CNF.NClause := [(45,false),(89,false),(79,true),(72,false),(70,true),(86,false)]
theorem der_34800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34800 :=
  CNF.rup_sound cl_34800 [cl_29634,cl_34322] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29634 v h) (hints_cons _ _ _ (der_34322 v h) (by intro d hd; cases hd)))
def cl_34801 : CNF.NClause := [(45,false),(89,false),(63,true),(70,true),(86,false),(14,false)]
theorem der_34801 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34801 :=
  CNF.rup_sound cl_34801 [cl_29636,cl_34798] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29636 v h) (hints_cons _ _ _ (der_34798 v h) (by intro d hd; cases hd)))
def cl_34802 : CNF.NClause := [(45,false),(86,true),(72,false),(89,false),(79,false),(70,false)]
theorem der_34802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34802 :=
  CNF.rup_sound cl_34802 [cl_29637,cl_29046] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29637 v h) (hints_cons _ _ _ (der_29046 v h) (by intro d hd; cases hd)))
def cl_34803 : CNF.NClause := [(45,false),(72,false),(86,true),(89,false),(79,false),(14,false)]
theorem der_34803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34803 :=
  CNF.rup_sound cl_34803 [cl_29638,cl_34324] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29638 v h) (hints_cons _ _ _ (der_34324 v h) (by intro d hd; cases hd)))
def cl_34804 : CNF.NClause := [(45,false),(72,true),(86,true),(70,true),(89,false),(79,false)]
theorem der_34804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34804 :=
  CNF.rup_sound cl_34804 [cl_29640,cl_34325] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29640 v h) (hints_cons _ _ _ (der_34325 v h) (by intro d hd; cases hd)))
def cl_34805 : CNF.NClause := [(45,false),(86,true),(63,true),(72,false),(89,false),(70,false)]
theorem der_34805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34805 :=
  CNF.rup_sound cl_34805 [cl_29641,cl_29073] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29641 v h) (hints_cons _ _ _ (der_29073 v h) (by intro d hd; cases hd)))
def cl_34806 : CNF.NClause := [(45,false),(89,false),(79,true),(72,false),(70,true),(14,false)]
theorem der_34806 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34806 :=
  CNF.rup_sound cl_34806 [cl_29642,cl_34800] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29642 v h) (hints_cons _ _ _ (der_34800 v h) (by intro d hd; cases hd)))
def cl_34807 : CNF.NClause := [(45,false),(89,false),(79,true),(63,true),(86,true),(70,false)]
theorem der_34807 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34807 :=
  CNF.rup_sound cl_34807 [cl_29643,cl_34805] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29643 v h) (hints_cons _ _ _ (der_34805 v h) (by intro d hd; cases hd)))
def cl_34808 : CNF.NClause := [(45,false),(63,true),(86,true),(70,true),(72,true),(89,false)]
theorem der_34808 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34808 :=
  CNF.rup_sound cl_34808 [cl_29644,cl_34804] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29644 v h) (hints_cons _ _ _ (der_34804 v h) (by intro d hd; cases hd)))
def cl_34809 : CNF.NClause := [(45,false),(79,false),(72,false),(70,true),(86,false),(89,true)]
theorem der_34809 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34809 :=
  CNF.rup_sound cl_34809 [cl_29646,cl_34328] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29646 v h) (hints_cons _ _ _ (der_34328 v h) (by intro d hd; cases hd)))
def cl_34810 : CNF.NClause := [(45,false),(79,false),(86,false),(14,false),(70,false),(89,true)]
theorem der_34810 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34810 :=
  CNF.rup_sound cl_34810 [cl_29647,cl_29645] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29647 v h) (hints_cons _ _ _ (der_29645 v h) (by intro d hd; cases hd)))
def cl_34811 : CNF.NClause := [(45,false),(86,false),(79,false),(70,true),(14,false),(89,true)]
theorem der_34811 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34811 :=
  CNF.rup_sound cl_34811 [cl_29648,cl_34809] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29648 v h) (hints_cons _ _ _ (der_34809 v h) (by intro d hd; cases hd)))
def cl_34812 : CNF.NClause := [(45,false),(70,false),(72,false),(86,false),(14,false),(79,true)]
theorem der_34812 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34812 :=
  CNF.rup_sound cl_34812 [cl_29649,cl_34799] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29649 v h) (hints_cons _ _ _ (der_34799 v h) (by intro d hd; cases hd)))
def cl_34813 : CNF.NClause := [(45,false),(86,false),(79,true),(63,true),(72,false),(70,true)]
theorem der_34813 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34813 :=
  CNF.rup_sound cl_34813 [cl_29650,cl_34800] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29650 v h) (hints_cons _ _ _ (der_34800 v h) (by intro d hd; cases hd)))
def cl_34816 : CNF.NClause := [(45,false),(86,true),(72,false),(79,false),(14,false),(70,false)]
theorem der_34816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34816 :=
  CNF.rup_sound cl_34816 [cl_29653,cl_34293] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29653 v h) (hints_cons _ _ _ (der_34293 v h) (by intro d hd; cases hd)))
def cl_34818 : CNF.NClause := [(45,false),(89,true),(79,false),(14,false),(70,false),(86,true)]
theorem der_34818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34818 :=
  CNF.rup_sound cl_34818 [cl_29655,cl_34816] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29655 v h) (hints_cons _ _ _ (der_34816 v h) (by intro d hd; cases hd)))
def cl_34819 : CNF.NClause := [(45,false),(79,false),(86,true),(63,true),(70,true),(89,true)]
theorem der_34819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34819 :=
  CNF.rup_sound cl_34819 [cl_29656,cl_34348] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29656 v h) (hints_cons _ _ _ (der_34348 v h) (by intro d hd; cases hd)))
def cl_34821 : CNF.NClause := [(45,false),(72,false),(86,true),(63,true),(70,true),(89,true)]
theorem der_34821 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34821 :=
  CNF.rup_sound cl_34821 [cl_29658,cl_34819] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29658 v h) (hints_cons _ _ _ (der_34819 v h) (by intro d hd; cases hd)))
def cl_34824 : CNF.NClause := [(45,false),(89,true),(72,false),(79,false),(86,false),(14,true)]
theorem der_34824 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34824 :=
  CNF.rup_sound cl_34824 [cl_29661,cl_34343] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29661 v h) (hints_cons _ _ _ (der_34343 v h) (by intro d hd; cases hd)))
def cl_34825 : CNF.NClause := [(45,false),(86,false),(63,true),(72,true),(14,true),(79,false)]
theorem der_34825 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34825 :=
  CNF.rup_sound cl_34825 [cl_29662,cl_34344] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29662 v h) (hints_cons _ _ _ (der_34344 v h) (by intro d hd; cases hd)))
def cl_34826 : CNF.NClause := [(45,false),(86,false),(79,true),(72,false),(14,true),(89,true)]
theorem der_34826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34826 :=
  CNF.rup_sound cl_34826 [cl_29663,cl_34311] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29663 v h) (hints_cons _ _ _ (der_34311 v h) (by intro d hd; cases hd)))
def cl_34827 : CNF.NClause := [(45,false),(70,false),(79,true),(72,true),(86,false),(14,true)]
theorem der_34827 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34827 :=
  CNF.rup_sound cl_34827 [cl_29664,cl_34684] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29664 v h) (hints_cons _ _ _ (der_34684 v h) (by intro d hd; cases hd)))
def cl_34828 : CNF.NClause := [(45,false),(79,false),(86,true),(14,true),(72,false),(89,true)]
theorem der_34828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34828 :=
  CNF.rup_sound cl_34828 [cl_29665,cl_34332] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29665 v h) (hints_cons _ _ _ (der_34332 v h) (by intro d hd; cases hd)))
def cl_34829 : CNF.NClause := [(45,false),(86,true),(72,true),(14,true),(79,false),(89,true)]
theorem der_34829 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34829 :=
  CNF.rup_sound cl_34829 [cl_29666,cl_34348] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29666 v h) (hints_cons _ _ _ (der_34348 v h) (by intro d hd; cases hd)))
def cl_34830 : CNF.NClause := [(45,false),(70,false),(86,true),(72,false),(14,true),(89,true)]
theorem der_34830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34830 :=
  CNF.rup_sound cl_34830 [cl_29667,cl_34828] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29667 v h) (hints_cons _ _ _ (der_34828 v h) (by intro d hd; cases hd)))
def cl_34831 : CNF.NClause := [(45,false),(70,false),(79,true),(63,true),(14,true),(72,true)]
theorem der_34831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34831 :=
  CNF.rup_sound cl_34831 [cl_29668,cl_34827] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29668 v h) (hints_cons _ _ _ (der_34827 v h) (by intro d hd; cases hd)))
def cl_34832 : CNF.NClause := [(45,false),(79,false),(72,false),(14,true),(89,false),(86,false)]
theorem der_34832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34832 :=
  CNF.rup_sound cl_34832 [cl_29669,cl_34343] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29669 v h) (hints_cons _ _ _ (der_34343 v h) (by intro d hd; cases hd)))
def cl_34839 : CNF.NClause := [(36,false),(58,false),(43,false),(52,false),(34,true),(116,true)]
theorem der_34839 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34839 :=
  CNF.rup_sound cl_34839 [cl_3458,cl_31325] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3458 v h) (hints_cons _ _ _ (der_31325 v h) (by intro d hd; cases hd)))
def cl_34840 : CNF.NClause := [(75,false),(53,false),(67,false),(78,false),(86,false),(22,true)]
theorem der_34840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34840 :=
  CNF.rup_sound cl_34840 [cl_29670,cl_32410] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29670 v h) (hints_cons _ _ _ (der_32410 v h) (by intro d hd; cases hd)))
def cl_34841 : CNF.NClause := [(75,true),(53,false),(90,false),(67,false),(78,false),(86,false)]
theorem der_34841 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34841 :=
  CNF.rup_sound cl_34841 [cl_29672,cl_29468] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29672 v h) (hints_cons _ _ _ (der_29468 v h) (by intro d hd; cases hd)))
def cl_34842 : CNF.NClause := [(53,false),(64,true),(90,false),(78,false),(86,false),(67,true)]
theorem der_34842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34842 :=
  CNF.rup_sound cl_34842 [cl_29673,cl_29671] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29673 v h) (hints_cons _ _ _ (der_29671 v h) (by intro d hd; cases hd)))
def cl_34843 : CNF.NClause := [(78,true),(53,false),(90,false),(67,false),(86,false),(75,false)]
theorem der_34843 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34843 :=
  CNF.rup_sound cl_34843 [cl_29674,cl_29090] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29674 v h) (hints_cons _ _ _ (der_29090 v h) (by intro d hd; cases hd)))
def cl_34844 : CNF.NClause := [(75,false),(64,true),(90,false),(86,false),(53,false),(67,true)]
theorem der_34844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34844 :=
  CNF.rup_sound cl_34844 [cl_29675,cl_29671] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29675 v h) (hints_cons _ _ _ (der_29671 v h) (by intro d hd; cases hd)))
def cl_34845 : CNF.NClause := [(78,true),(53,false),(75,true),(90,false),(67,false),(86,false)]
theorem der_34845 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34845 :=
  CNF.rup_sound cl_34845 [cl_29676,cl_34642] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29676 v h) (hints_cons _ _ _ (der_34642 v h) (by intro d hd; cases hd)))
def cl_34846 : CNF.NClause := [(78,true),(86,false),(64,true),(75,true),(90,false),(53,false)]
theorem der_34846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34846 :=
  CNF.rup_sound cl_34846 [cl_29677,cl_34845] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29677 v h) (hints_cons _ _ _ (der_34845 v h) (by intro d hd; cases hd)))
def cl_34847 : CNF.NClause := [(90,false),(53,false),(86,true),(67,false),(78,false),(75,false)]
theorem der_34847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34847 :=
  CNF.rup_sound cl_34847 [cl_29678,cl_34785] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29678 v h) (hints_cons _ _ _ (der_34785 v h) (by intro d hd; cases hd)))
def cl_34848 : CNF.NClause := [(53,false),(67,true),(64,true),(90,false),(78,false),(75,false)]
theorem der_34848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34848 :=
  CNF.rup_sound cl_34848 [cl_29679,cl_29671] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29679 v h) (hints_cons _ _ _ (der_29671 v h) (by intro d hd; cases hd)))
def cl_34849 : CNF.NClause := [(53,false),(67,false),(75,true),(90,false),(86,true),(78,false)]
theorem der_34849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34849 :=
  CNF.rup_sound cl_34849 [cl_29680,cl_34643] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29680 v h) (hints_cons _ _ _ (der_34643 v h) (by intro d hd; cases hd)))
def cl_34850 : CNF.NClause := [(53,false),(67,true),(64,true),(90,false),(78,false),(86,true)]
theorem der_34850 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34850 :=
  CNF.rup_sound cl_34850 [cl_29681,cl_34773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29681 v h) (hints_cons _ _ _ (der_34773 v h) (by intro d hd; cases hd)))
def cl_34851 : CNF.NClause := [(78,true),(75,false),(64,true),(90,false),(67,false),(53,false)]
theorem der_34851 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34851 :=
  CNF.rup_sound cl_34851 [cl_29682,cl_34843] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29682 v h) (hints_cons _ _ _ (der_34843 v h) (by intro d hd; cases hd)))
def cl_34852 : CNF.NClause := [(75,false),(86,true),(64,true),(90,false),(53,false),(67,true)]
theorem der_34852 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34852 :=
  CNF.rup_sound cl_34852 [cl_29683,cl_34850] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29683 v h) (hints_cons _ _ _ (der_34850 v h) (by intro d hd; cases hd)))
def cl_34853 : CNF.NClause := [(78,true),(90,false),(75,true),(22,false),(53,false),(67,false)]
theorem der_34853 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34853 :=
  CNF.rup_sound cl_34853 [cl_29684,cl_34845] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29684 v h) (hints_cons _ _ _ (der_34845 v h) (by intro d hd; cases hd)))
def cl_34854 : CNF.NClause := [(78,true),(90,false),(86,true),(75,true),(53,false),(67,true)]
theorem der_34854 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34854 :=
  CNF.rup_sound cl_34854 [cl_29685,cl_34788] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29685 v h) (hints_cons _ _ _ (der_34788 v h) (by intro d hd; cases hd)))
def cl_34855 : CNF.NClause := [(78,false),(53,false),(67,false),(86,false),(75,false),(90,true)]
theorem der_34855 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34855 :=
  CNF.rup_sound cl_34855 [cl_29686,cl_34789] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29686 v h) (hints_cons _ _ _ (der_34789 v h) (by intro d hd; cases hd)))
def cl_34856 : CNF.NClause := [(86,false),(53,false),(78,false),(64,true),(75,false),(67,true)]
theorem der_34856 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34856 :=
  CNF.rup_sound cl_34856 [cl_29687,cl_34848] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29687 v h) (hints_cons _ _ _ (der_34848 v h) (by intro d hd; cases hd)))
def cl_34857 : CNF.NClause := [(75,true),(86,false),(67,false),(78,false),(53,false),(90,true)]
theorem der_34857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34857 :=
  CNF.rup_sound cl_34857 [cl_29688,cl_34659] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29688 v h) (hints_cons _ _ _ (der_34659 v h) (by intro d hd; cases hd)))
def cl_34858 : CNF.NClause := [(75,true),(53,false),(22,false),(78,false),(86,false),(90,true)]
theorem der_34858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34858 :=
  CNF.rup_sound cl_34858 [cl_29689,cl_34857] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29689 v h) (hints_cons _ _ _ (der_34857 v h) (by intro d hd; cases hd)))
def cl_34859 : CNF.NClause := [(78,true),(53,false),(67,false),(86,false),(75,false),(90,true)]
theorem der_34859 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34859 :=
  CNF.rup_sound cl_34859 [cl_29690,cl_34314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29690 v h) (hints_cons _ _ _ (der_34314 v h) (by intro d hd; cases hd)))
def cl_34860 : CNF.NClause := [(78,true),(53,false),(64,true),(86,false),(75,false),(90,true)]
theorem der_34860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34860 :=
  CNF.rup_sound cl_34860 [cl_29691,cl_34859] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29691 v h) (hints_cons _ _ _ (der_34859 v h) (by intro d hd; cases hd)))
def cl_34861 : CNF.NClause := [(78,true),(86,false),(75,true),(22,false),(67,false),(53,false)]
theorem der_34861 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34861 :=
  CNF.rup_sound cl_34861 [cl_29692,cl_34845] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29692 v h) (hints_cons _ _ _ (der_34845 v h) (by intro d hd; cases hd)))
def cl_34862 : CNF.NClause := [(53,false),(75,true),(22,false),(86,false),(67,true),(90,true)]
theorem der_34862 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34862 :=
  CNF.rup_sound cl_34862 [cl_29693,cl_34858] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29693 v h) (hints_cons _ _ _ (der_34858 v h) (by intro d hd; cases hd)))
def cl_34863 : CNF.NClause := [(78,false),(53,false),(22,false),(67,false),(75,false),(90,true)]
theorem der_34863 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34863 :=
  CNF.rup_sound cl_34863 [cl_29694,cl_34292] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29694 v h) (hints_cons _ _ _ (der_34292 v h) (by intro d hd; cases hd)))
def cl_34864 : CNF.NClause := [(90,true),(53,false),(22,false),(78,false),(75,false),(86,true)]
theorem der_34864 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34864 :=
  CNF.rup_sound cl_34864 [cl_29695,cl_34793] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29695 v h) (hints_cons _ _ _ (der_34793 v h) (by intro d hd; cases hd)))
def cl_34867 : CNF.NClause := [(78,true),(90,true),(22,false),(67,false),(75,false),(53,false)]
theorem der_34867 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34867 :=
  CNF.rup_sound cl_34867 [cl_29698,cl_34859] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29698 v h) (hints_cons _ _ _ (der_34859 v h) (by intro d hd; cases hd)))
def cl_34868 : CNF.NClause := [(78,true),(75,false),(86,true),(64,true),(53,false),(67,true)]
theorem der_34868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34868 :=
  CNF.rup_sound cl_34868 [cl_29699,cl_29612] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29699 v h) (hints_cons _ _ _ (der_29612 v h) (by intro d hd; cases hd)))
def cl_34874 : CNF.NClause := [(37,false),(46,false),(44,false),(53,false),(35,true),(109,true)]
theorem der_34874 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34874 :=
  CNF.rup_sound cl_34874 [cl_3010,cl_31751] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3010 v h) (hints_cons _ _ _ (der_31751 v h) (by intro d hd; cases hd)))
def cl_34875 : CNF.NClause := [(46,false),(15,true),(92,false),(78,false),(79,false),(81,false),(80,false)]
theorem der_34875 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34875 :=
  CNF.rup_sound cl_34875 [cl_5890,cl_32911] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5890 v h) (hints_cons _ _ _ (der_32911 v h) (by intro d hd; cases hd)))
def cl_34876 : CNF.NClause := [(32,false),(71,false),(1,false),(86,false),(66,false),(76,false),(87,true)]
theorem der_34876 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34876 :=
  CNF.rup_sound cl_34876 [cl_4161,cl_28991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4161 v h) (hints_cons _ _ _ (der_28991 v h) (by intro d hd; cases hd)))
def cl_34882 : CNF.NClause := [(39,false),(68,true),(90,false),(79,false),(82,false),(76,false),(65,false)]
theorem der_34882 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34882 :=
  CNF.rup_sound cl_34882 [cl_4997,cl_32128] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4997 v h) (hints_cons _ _ _ (der_32128 v h) (by intro d hd; cases hd)))
def cl_34883 : CNF.NClause := [(39,false),(79,true),(90,false),(82,false),(76,false),(68,false),(65,false)]
theorem der_34883 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34883 :=
  CNF.rup_sound cl_34883 [cl_5009,cl_32157] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5009 v h) (hints_cons _ _ _ (der_32157 v h) (by intro d hd; cases hd)))
def cl_34884 : CNF.NClause := [(39,false),(90,false),(79,false),(76,false),(82,true),(8,false),(68,false)]
theorem der_34884 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34884 :=
  CNF.rup_sound cl_34884 [cl_5025,cl_26409] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5025 v h) (hints_cons _ _ _ (der_26409 v h) (by intro d hd; cases hd)))
def cl_34885 : CNF.NClause := [(39,false),(76,false),(79,false),(8,false),(82,false),(68,false),(90,true)]
theorem der_34885 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34885 :=
  CNF.rup_sound cl_34885 [cl_5057,cl_32144] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5057 v h) (hints_cons _ _ _ (der_32144 v h) (by intro d hd; cases hd)))
def cl_34886 : CNF.NClause := [(37,false),(74,false),(91,false),(78,false),(82,false),(66,false),(70,true)]
theorem der_34886 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34886 :=
  CNF.rup_sound cl_34886 [cl_4741,cl_26488] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4741 v h) (hints_cons _ _ _ (der_26488 v h) (by intro d hd; cases hd)))
def cl_34887 : CNF.NClause := [(37,false),(74,true),(91,false),(78,false),(82,false),(6,false),(70,false)]
theorem der_34887 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34887 :=
  CNF.rup_sound cl_34887 [cl_4745,cl_32219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4745 v h) (hints_cons _ _ _ (der_32219 v h) (by intro d hd; cases hd)))
def cl_34888 : CNF.NClause := [(37,false),(78,true),(91,false),(66,false),(6,false),(74,false),(70,false)]
theorem der_34888 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34888 :=
  CNF.rup_sound cl_34888 [cl_4753,cl_26529] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4753 v h) (hints_cons _ _ _ (der_26529 v h) (by intro d hd; cases hd)))
def cl_34890 : CNF.NClause := [(37,false),(82,false),(66,false),(6,false),(74,false),(70,false),(91,true)]
theorem der_34890 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34890 :=
  CNF.rup_sound cl_34890 [cl_4801,cl_26558] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4801 v h) (hints_cons _ _ _ (der_26558 v h) (by intro d hd; cases hd)))
def cl_34891 : CNF.NClause := [(36,false),(92,false),(5,false),(82,false),(86,false),(84,false),(83,true)]
theorem der_34891 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34891 :=
  CNF.rup_sound cl_34891 [cl_4613,cl_32349] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4613 v h) (hints_cons _ _ _ (der_32349 v h) (by intro d hd; cases hd)))
def cl_34892 : CNF.NClause := [(36,false),(84,true),(92,false),(85,false),(82,false),(86,false),(5,false)]
theorem der_34892 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34892 :=
  CNF.rup_sound cl_34892 [cl_4617,cl_26675] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4617 v h) (hints_cons _ _ _ (der_26675 v h) (by intro d hd; cases hd)))
def cl_34893 : CNF.NClause := [(36,false),(82,false),(92,false),(85,false),(86,true),(84,false),(83,false)]
theorem der_34893 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34893 :=
  CNF.rup_sound cl_34893 [cl_4641,cl_32334] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4641 v h) (hints_cons _ _ _ (der_32334 v h) (by intro d hd; cases hd)))
def cl_34894 : CNF.NClause := [(52,false),(67,false),(79,false),(66,false),(73,false),(21,false),(88,true)]
theorem der_34894 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34894 :=
  CNF.rup_sound cl_34894 [cl_6721,cl_34299] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6721 v h) (hints_cons _ _ _ (der_34299 v h) (by intro d hd; cases hd)))
def cl_34896 : CNF.NClause := [(54,false),(67,false),(23,true),(89,false),(81,false),(83,false),(65,false)]
theorem der_34896 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34896 :=
  CNF.rup_sound cl_34896 [cl_6914,cl_32545] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6914 v h) (hints_cons _ _ _ (der_32545 v h) (by intro d hd; cases hd)))
def cl_34900 : CNF.NClause := [(58,false),(69,true),(27,false),(89,false),(62,false),(78,false),(76,false)]
theorem der_34900 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34900 :=
  CNF.rup_sound cl_34900 [cl_7429,cl_32475] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7429 v h) (hints_cons _ _ _ (der_32475 v h) (by intro d hd; cases hd)))
def cl_34904 : CNF.NClause := [(54,false),(65,true),(67,false),(89,false),(74,false),(81,false),(23,false)]
theorem der_34904 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34904 :=
  CNF.rup_sound cl_34904 [cl_6915,cl_32601] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6915 v h) (hints_cons _ _ _ (der_32601 v h) (by intro d hd; cases hd)))
def cl_34905 : CNF.NClause := [(54,false),(74,false),(89,false),(23,false),(83,false),(67,true),(65,false)]
theorem der_34905 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34905 :=
  CNF.rup_sound cl_34905 [cl_6917,cl_32588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6917 v h) (hints_cons _ _ _ (der_32588 v h) (by intro d hd; cases hd)))
def cl_34906 : CNF.NClause := [(54,false),(81,true),(67,false),(89,false),(23,false),(83,false),(65,false)]
theorem der_34906 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34906 :=
  CNF.rup_sound cl_34906 [cl_6929,cl_32545] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6929 v h) (hints_cons _ _ _ (der_32545 v h) (by intro d hd; cases hd)))
def cl_34908 : CNF.NClause := [(54,false),(83,false),(67,false),(74,false),(23,false),(89,true),(65,false)]
theorem der_34908 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34908 :=
  CNF.rup_sound cl_34908 [cl_6977,cl_32588] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6977 v h) (hints_cons _ _ _ (der_32588 v h) (by intro d hd; cases hd)))
def cl_34909 : CNF.NClause := [(40,false),(88,false),(9,false),(63,true),(82,false),(69,false),(81,false)]
theorem der_34909 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34909 :=
  CNF.rup_sound cl_34909 [cl_5123,cl_32660] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5123 v h) (hints_cons _ _ _ (der_32660 v h) (by intro d hd; cases hd)))
def cl_34910 : CNF.NClause := [(40,false),(69,false),(63,false),(9,false),(88,false),(81,false),(82,true)]
theorem der_34910 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34910 :=
  CNF.rup_sound cl_34910 [cl_5153,cl_32660] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5153 v h) (hints_cons _ _ _ (der_32660 v h) (by intro d hd; cases hd)))
def cl_34911 : CNF.NClause := [(40,false),(88,true),(63,false),(82,false),(69,false),(75,false),(9,false)]
theorem der_34911 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34911 :=
  CNF.rup_sound cl_34911 [cl_5185,cl_32686] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5185 v h) (hints_cons _ _ _ (der_32686 v h) (by intro d hd; cases hd)))
def cl_34912 : CNF.NClause := [(60,false),(62,false),(29,true),(88,false),(86,false),(80,false),(68,false)]
theorem der_34912 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34912 :=
  CNF.rup_sound cl_34912 [cl_7682,cl_32725] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7682 v h) (hints_cons _ _ _ (der_32725 v h) (by intro d hd; cases hd)))
def cl_34913 : CNF.NClause := [(60,false),(68,true),(29,false),(88,false),(62,false),(86,false),(80,false)]
theorem der_34913 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34913 :=
  CNF.rup_sound cl_34913 [cl_7685,cl_32737] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7685 v h) (hints_cons _ _ _ (der_32737 v h) (by intro d hd; cases hd)))
def cl_34914 : CNF.NClause := [(60,false),(80,true),(29,false),(88,false),(62,false),(86,false),(68,false)]
theorem der_34914 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34914 :=
  CNF.rup_sound cl_34914 [cl_7697,cl_32725] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7697 v h) (hints_cons _ _ _ (der_32725 v h) (by intro d hd; cases hd)))
def cl_34915 : CNF.NClause := [(60,false),(88,false),(29,false),(86,true),(62,false),(74,false),(80,false)]
theorem der_34915 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34915 :=
  CNF.rup_sound cl_34915 [cl_7713,cl_32742] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7713 v h) (hints_cons _ _ _ (der_32742 v h) (by intro d hd; cases hd)))
def cl_34916 : CNF.NClause := [(60,false),(86,false),(29,false),(62,false),(80,false),(68,false),(88,true)]
theorem der_34916 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34916 :=
  CNF.rup_sound cl_34916 [cl_7745,cl_32760] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7745 v h) (hints_cons _ _ _ (der_32760 v h) (by intro d hd; cases hd)))
def cl_34919 : CNF.NClause := [(55,false),(80,true),(24,false),(91,false),(67,false),(84,false),(76,false)]
theorem der_34919 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34919 :=
  CNF.rup_sound cl_34919 [cl_7057,cl_32811] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7057 v h) (hints_cons _ _ _ (der_32811 v h) (by intro d hd; cases hd)))
def cl_34920 : CNF.NClause := [(55,false),(76,false),(67,false),(84,false),(24,false),(80,false),(91,true)]
theorem der_34920 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34920 :=
  CNF.rup_sound cl_34920 [cl_7105,cl_32855] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7105 v h) (hints_cons _ _ _ (der_32855 v h) (by intro d hd; cases hd)))
def cl_34921 : CNF.NClause := [(46,false),(78,false),(79,true),(92,false),(15,false),(81,false),(80,false)]
theorem der_34921 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34921 :=
  CNF.rup_sound cl_34921 [cl_5897,cl_32916] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5897 v h) (hints_cons _ _ _ (der_32916 v h) (by intro d hd; cases hd)))
def cl_34923 : CNF.NClause := [(42,false),(90,false),(11,true),(72,false),(69,false),(83,false),(80,false)]
theorem der_34923 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34923 :=
  CNF.rup_sound cl_34923 [cl_5378,cl_32997] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5378 v h) (hints_cons _ _ _ (der_32997 v h) (by intro d hd; cases hd)))
def cl_34924 : CNF.NClause := [(42,false),(69,false),(72,true),(90,false),(11,false),(83,false),(80,false)]
theorem der_34924 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34924 :=
  CNF.rup_sound cl_34924 [cl_5385,cl_32991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5385 v h) (hints_cons _ _ _ (der_32991 v h) (by intro d hd; cases hd)))
def cl_34925 : CNF.NClause := [(42,false),(80,true),(11,false),(72,false),(90,false),(69,false),(83,false)]
theorem der_34925 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34925 :=
  CNF.rup_sound cl_34925 [cl_5393,cl_32991] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5393 v h) (hints_cons _ _ _ (der_32991 v h) (by intro d hd; cases hd)))
def cl_34927 : CNF.NClause := [(42,false),(69,false),(72,false),(11,false),(83,false),(80,false),(90,true)]
theorem der_34927 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34927 :=
  CNF.rup_sound cl_34927 [cl_5441,cl_33028] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5441 v h) (hints_cons _ _ _ (der_33028 v h) (by intro d hd; cases hd)))
def cl_34928 : CNF.NClause := [(34,false),(75,false),(85,false),(3,true),(87,false),(70,false),(65,false)]
theorem der_34928 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34928 :=
  CNF.rup_sound cl_34928 [cl_4354,cl_33070] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4354 v h) (hints_cons _ _ _ (der_33070 v h) (by intro d hd; cases hd)))
def cl_34931 : CNF.NClause := [(34,false),(75,true),(3,false),(85,false),(87,false),(70,false),(65,false)]
theorem der_34931 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34931 :=
  CNF.rup_sound cl_34931 [cl_4361,cl_33074] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4361 v h) (hints_cons _ _ _ (der_33074 v h) (by intro d hd; cases hd)))
def cl_34933 : CNF.NClause := [(34,false),(85,false),(3,false),(75,false),(80,false),(65,false),(87,true)]
theorem der_34933 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34933 :=
  CNF.rup_sound cl_34933 [cl_4417,cl_33106] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4417 v h) (hints_cons _ _ _ (der_33106 v h) (by intro d hd; cases hd)))
def cl_34934 : CNF.NClause := [(48,false),(77,false),(64,true),(17,false),(88,false),(76,false),(83,false)]
theorem der_34934 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34934 :=
  CNF.rup_sound cl_34934 [cl_6147,cl_33156] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6147 v h) (hints_cons _ _ _ (der_33156 v h) (by intro d hd; cases hd)))
def cl_34935 : CNF.NClause := [(48,false),(76,false),(17,false),(64,false),(83,false),(70,false),(88,true)]
theorem der_34935 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34935 :=
  CNF.rup_sound cl_34935 [cl_6209,cl_27825] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6209 v h) (hints_cons _ _ _ (der_27825 v h) (by intro d hd; cases hd)))
def cl_34936 : CNF.NClause := [(43,false),(12,true),(91,false),(72,false),(85,false),(81,false),(68,false)]
theorem der_34936 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34936 :=
  CNF.rup_sound cl_34936 [cl_5506,cl_27868] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5506 v h) (hints_cons _ _ _ (der_27868 v h) (by intro d hd; cases hd)))
def cl_34938 : CNF.NClause := [(43,false),(91,false),(12,false),(72,false),(64,false),(81,false),(85,true)]
theorem der_34938 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34938 :=
  CNF.rup_sound cl_34938 [cl_5537,cl_33275] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5537 v h) (hints_cons _ _ _ (der_33275 v h) (by intro d hd; cases hd)))
def cl_34939 : CNF.NClause := [(43,false),(85,false),(12,false),(64,false),(81,false),(68,false),(91,true)]
theorem der_34939 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34939 :=
  CNF.rup_sound cl_34939 [cl_5569,cl_33293] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5569 v h) (hints_cons _ _ _ (der_33293 v h) (by intro d hd; cases hd)))
def cl_34941 : CNF.NClause := [(33,false),(64,false),(87,false),(69,false),(84,false),(79,true),(2,false)]
theorem der_34941 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34941 :=
  CNF.rup_sound cl_34941 [cl_4241,cl_33369] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4241 v h) (hints_cons _ _ _ (der_33369 v h) (by intro d hd; cases hd)))
def cl_34942 : CNF.NClause := [(33,false),(79,false),(69,false),(84,false),(74,false),(2,false),(87,true)]
theorem der_34942 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34942 :=
  CNF.rup_sound cl_34942 [cl_4289,cl_33404] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4289 v h) (hints_cons _ _ _ (der_33404 v h) (by intro d hd; cases hd)))
def cl_34943 : CNF.NClause := [(38,false),(64,true),(89,false),(82,false),(71,false),(73,false),(80,false)]
theorem der_34943 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34943 :=
  CNF.rup_sound cl_34943 [cl_4867,cl_33435] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4867 v h) (hints_cons _ _ _ (der_33435 v h) (by intro d hd; cases hd)))
def cl_34945 : CNF.NClause := [(38,false),(80,true),(89,false),(64,false),(82,false),(73,false),(7,false)]
theorem der_34945 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34945 :=
  CNF.rup_sound cl_34945 [cl_4881,cl_33454] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4881 v h) (hints_cons _ _ _ (der_33454 v h) (by intro d hd; cases hd)))
def cl_34946 : CNF.NClause := [(38,false),(89,false),(64,false),(71,false),(80,false),(82,true),(7,false)]
theorem der_34946 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34946 :=
  CNF.rup_sound cl_34946 [cl_4897,cl_28140] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4897 v h) (hints_cons _ _ _ (der_28140 v h) (by intro d hd; cases hd)))
def cl_34947 : CNF.NClause := [(38,false),(82,false),(64,false),(71,false),(73,false),(80,false),(89,true)]
theorem der_34947 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34947 :=
  CNF.rup_sound cl_34947 [cl_4929,cl_33466] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4929 v h) (hints_cons _ _ _ (der_33466 v h) (by intro d hd; cases hd)))
def cl_34949 : CNF.NClause := [(59,false),(84,true),(28,false),(90,false),(62,false),(81,false),(70,false)]
theorem der_34949 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34949 :=
  CNF.rup_sound cl_34949 [cl_7585,cl_33535] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7585 v h) (hints_cons _ _ _ (der_33535 v h) (by intro d hd; cases hd)))
def cl_34950 : CNF.NClause := [(59,false),(73,false),(28,false),(62,false),(84,false),(81,false),(90,true)]
theorem der_34950 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34950 :=
  CNF.rup_sound cl_34950 [cl_7617,cl_33562] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7617 v h) (hints_cons _ _ _ (der_33562 v h) (by intro d hd; cases hd)))
def cl_34951 : CNF.NClause := [(41,false),(73,false),(10,false),(75,false),(74,false),(76,false),(92,true)]
theorem der_34951 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34951 :=
  CNF.rup_sound cl_34951 [cl_5313,cl_33654] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5313 v h) (hints_cons _ _ _ (der_33654 v h) (by intro d hd; cases hd)))
def cl_34953 : CNF.NClause := [(35,false),(78,false),(4,false),(63,false),(83,false),(68,false),(87,true)]
theorem der_34953 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34953 :=
  CNF.rup_sound cl_34953 [cl_4545,cl_28527] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4545 v h) (hints_cons _ _ _ (der_28527 v h) (by intro d hd; cases hd)))
def cl_34954 : CNF.NClause := [(57,false),(75,false),(62,false),(79,false),(26,false),(83,false),(91,true)]
theorem der_34954 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34954 :=
  CNF.rup_sound cl_34954 [cl_7361,cl_33841] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7361 v h) (hints_cons _ _ _ (der_33841 v h) (by intro d hd; cases hd)))
def cl_34955 : CNF.NClause := [(51,false),(20,true),(92,false),(71,false),(69,false),(70,false),(68,false)]
theorem der_34955 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34955 :=
  CNF.rup_sound cl_34955 [cl_6530,cl_28687] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6530 v h) (hints_cons _ _ _ (der_28687 v h) (by intro d hd; cases hd)))
def cl_34956 : CNF.NClause := [(51,false),(71,false),(20,false),(69,false),(70,false),(68,false),(92,true)]
theorem der_34956 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34956 :=
  CNF.rup_sound cl_34956 [cl_6593,cl_33932] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6593 v h) (hints_cons _ _ _ (der_33932 v h) (by intro d hd; cases hd)))
def cl_34958 : CNF.NClause := [(32,false),(86,false),(71,true),(1,false),(87,false),(81,false),(76,false)]
theorem der_34958 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34958 :=
  CNF.rup_sound cl_34958 [cl_4101,cl_34077] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4101 v h) (hints_cons _ _ _ (der_34077 v h) (by intro d hd; cases hd)))
def cl_34960 : CNF.NClause := [(32,false),(81,true),(1,false),(87,false),(71,false),(86,false),(76,false)]
theorem der_34960 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34960 :=
  CNF.rup_sound cl_34960 [cl_4113,cl_34080] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4113 v h) (hints_cons _ _ _ (der_34080 v h) (by intro d hd; cases hd)))
def cl_34961 : CNF.NClause := [(32,false),(71,false),(86,true),(1,false),(87,false),(81,false),(76,false)]
theorem der_34961 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34961 :=
  CNF.rup_sound cl_34961 [cl_4129,cl_34087] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4129 v h) (hints_cons _ _ _ (der_34087 v h) (by intro d hd; cases hd)))
def cl_34962 : CNF.NClause := [(49,false),(86,true),(91,false),(69,false),(73,false),(18,false),(65,false)]
theorem der_34962 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34962 :=
  CNF.rup_sound cl_34962 [cl_6305,cl_29051] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6305 v h) (hints_cons _ _ _ (der_29051 v h) (by intro d hd; cases hd)))
def cl_34963 : CNF.NClause := [(45,false),(86,false),(79,true),(72,false),(14,true),(89,false),(70,false)]
theorem der_34963 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34963 :=
  CNF.rup_sound cl_34963 [cl_5780,cl_29078] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5780 v h) (hints_cons _ _ _ (der_29078 v h) (by intro d hd; cases hd)))
def cl_34966 : CNF.NClause := [(90,false),(53,false),(64,false),(78,false),(86,false),(75,false),(67,true)]
theorem der_34966 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34966 :=
  CNF.rup_sound cl_34966 [cl_6789,cl_29614] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6789 v h) (hints_cons _ _ _ (der_29614 v h) (by intro d hd; cases hd)))
def cl_34967 : CNF.NClause := [(78,false),(53,false),(64,true),(90,false),(22,true),(75,false),(67,true)]
theorem der_34967 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34967 :=
  CNF.rup_sound cl_34967 [cl_6792,cl_34850] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6792 v h) (hints_cons _ _ _ (der_34850 v h) (by intro d hd; cases hd)))
def cl_34968 : CNF.NClause := [(45,false),(86,false),(72,false),(89,false),(79,false),(63,true),(14,false)]
theorem der_34968 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34968 :=
  CNF.rup_sound cl_34968 [cl_5763,cl_34797] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_5763 v h) (hints_cons _ _ _ (der_34797 v h) (by intro d hd; cases hd)))
def cl_34969 : CNF.NClause := [(53,false),(64,true),(22,false),(67,false),(78,false),(86,false),(75,false)]
theorem der_34969 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34969 :=
  CNF.rup_sound cl_34969 [cl_6787,cl_34855] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_6787 v h) (hints_cons _ _ _ (der_34855 v h) (by intro d hd; cases hd)))
def cl_34974 : CNF.NClause := [(69,true),(27,false),(9,false),(11,false),(18,true)]
theorem der_34974 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34974 :=
  CNF.rup_sound cl_34974 [cl_23583,cl_30027] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23583 v h) (hints_cons _ _ _ (der_30027 v h) (by intro d hd; cases hd)))
def cl_34992 : CNF.NClause := [(107,true),(39,false),(58,false),(41,true)]
theorem der_34992 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34992 :=
  CNF.rup_sound cl_34992 [cl_31959,cl_31951] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31959 v h) (hints_cons _ _ _ (der_31951 v h) (by intro d hd; cases hd)))
def cl_34998 : CNF.NClause := [(48,false),(64,false),(88,false),(76,true),(77,false),(83,false)]
theorem der_34998 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_34998 :=
  CNF.rup_sound cl_34998 [cl_27763,cl_33158] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27763 v h) (hints_cons _ _ _ (der_33158 v h) (by intro d hd; cases hd)))
def cl_35000 : CNF.NClause := [(81,true),(23,false),(1,true),(15,false)]
theorem der_35000 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35000 :=
  CNF.rup_sound cl_35000 [cl_30334,cl_30508] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30334 v h) (hints_cons _ _ _ (der_30508 v h) (by intro d hd; cases hd)))
def cl_35013 : CNF.NClause := [(48,false),(64,false),(88,false),(83,false),(76,false),(17,true),(77,false)]
theorem der_35013 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35013 :=
  CNF.rup_sound cl_35013 [cl_26759,cl_27760] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26759 v h) (hints_cons _ _ _ (der_27760 v h) (by intro d hd; cases hd)))
def cl_35014 : CNF.NClause := [(100,true),(42,false),(40,false),(49,true)]
theorem der_35014 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35014 :=
  CNF.rup_sound cl_35014 [cl_31850,cl_31851] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31850 v h) (hints_cons _ _ _ (der_31851 v h) (by intro d hd; cases hd)))
def cl_35028 : CNF.NClause := [(67,true),(21,false),(24,true),(23,false)]
theorem der_35028 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35028 :=
  CNF.rup_sound cl_35028 [cl_29881,cl_29938] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29881 v h) (hints_cons _ _ _ (der_29938 v h) (by intro d hd; cases hd)))
def cl_35029 : CNF.NClause := [(91,true),(24,true),(18,false),(12,true),(6,false)]
theorem der_35029 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35029 :=
  CNF.rup_sound cl_35029 [cl_23357,cl_29893] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23357 v h) (hints_cons _ _ _ (der_29893 v h) (by intro d hd; cases hd)))
def cl_35030 : CNF.NClause := [(90,true),(19,true),(11,false),(8,false)]
theorem der_35030 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35030 :=
  CNF.rup_sound cl_35030 [cl_29922,cl_29923] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29922 v h) (hints_cons _ _ _ (der_29923 v h) (by intro d hd; cases hd)))
def cl_35035 : CNF.NClause := [(75,true),(22,true),(16,false),(10,true),(9,false),(3,true)]
theorem der_35035 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35035 :=
  CNF.rup_sound cl_35035 [cl_30550,cl_24500] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30550 v h) (hints_cons _ _ _ (der_24500 v h) (by intro d hd; cases hd)))
def cl_35043 : CNF.NClause := [(97,true),(42,false),(47,false),(52,false)]
theorem der_35043 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35043 :=
  CNF.rup_sound cl_35043 [cl_31911,cl_31912] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31911 v h) (hints_cons _ _ _ (der_31912 v h) (by intro d hd; cases hd)))
def cl_35044 : CNF.NClause := [(108,true),(47,false),(46,false),(49,false),(48,true),(61,true)]
theorem der_35044 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35044 :=
  CNF.rup_sound cl_35044 [cl_26147,cl_23859] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26147 v h) (hints_cons _ _ _ (der_23859 v h) (by intro d hd; cases hd)))
def cl_35045 : CNF.NClause := [(42,false),(108,false),(115,false),(99,false),(120,false),(47,false),(34,true),(40,false),(75,false),(52,false),(67,false),(64,false),(22,false),(69,false),(83,false),(86,false),(66,false),(78,false),(72,false),(11,false)]
theorem der_35045 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35045 :=
  CNF.rup_sound cl_35045 [cl_27591,cl_35043,cl_6785,cl_7953,cl_31273] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27591 v h) (hints_cons _ _ _ (der_35043 v h) (hints_cons _ _ _ (inp_6785 v h) (hints_cons _ _ _ (inp_7953 v h) (hints_cons _ _ _ (der_31273 v h) (by intro d hd; cases hd))))))
def cl_35046 : CNF.NClause := [(90,true),(22,false),(11,false),(8,false)]
theorem der_35046 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35046 :=
  CNF.rup_sound cl_35046 [cl_29910,cl_29921,cl_30007] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29910 v h) (hints_cons _ _ _ (der_29921 v h) (hints_cons _ _ _ (der_30007 v h) (by intro d hd; cases hd))))
def cl_35048 : CNF.NClause := [(75,true),(22,false),(3,true),(9,false)]
theorem der_35048 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35048 :=
  CNF.rup_sound cl_35048 [cl_30549,cl_30551] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30549 v h) (hints_cons _ _ _ (der_30551 v h) (by intro d hd; cases hd)))
def cl_35053 : CNF.NClause := [(91,true),(24,false),(18,false),(12,true),(6,false)]
theorem der_35053 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35053 :=
  CNF.rup_sound cl_35053 [cl_23354,cl_23357] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23354 v h) (hints_cons _ _ _ (der_23357 v h) (by intro d hd; cases hd)))
def cl_35055 : CNF.NClause := [(67,true),(21,false),(24,false),(23,false)]
theorem der_35055 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35055 :=
  CNF.rup_sound cl_35055 [cl_29881,cl_29941] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29881 v h) (hints_cons _ _ _ (der_29941 v h) (by intro d hd; cases hd)))
def cl_35058 : CNF.NClause := [(108,true),(49,false),(47,false),(61,true),(46,false)]
theorem der_35058 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35058 :=
  CNF.rup_sound cl_35058 [cl_23859,cl_31874,cl_35044] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23859 v h) (hints_cons _ _ _ (der_31874 v h) (hints_cons _ _ _ (der_35044 v h) (by intro d hd; cases hd))))
def cl_35060 : CNF.NClause := [(90,true),(22,true),(11,false),(8,false)]
theorem der_35060 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35060 :=
  CNF.rup_sound cl_35060 [cl_23212,cl_35030] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23212 v h) (hints_cons _ _ _ (der_35030 v h) (by intro d hd; cases hd)))
def cl_35062 : CNF.NClause := [(115,true),(36,false),(33,false),(47,false)]
theorem der_35062 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35062 :=
  CNF.rup_sound cl_35062 [cl_31559,cl_31884] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31559 v h) (hints_cons _ _ _ (der_31884 v h) (by intro d hd; cases hd)))
def cl_35065 : CNF.NClause := [(115,true),(36,true),(33,false),(47,false),(55,false)]
theorem der_35065 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35065 :=
  CNF.rup_sound cl_35065 [cl_30841,cl_30840] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30841 v h) (hints_cons _ _ _ (der_30840 v h) (by intro d hd; cases hd)))
def cl_35066 : CNF.NClause := [(120,true),(45,true),(54,false),(47,false),(31,true)]
theorem der_35066 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35066 :=
  CNF.rup_sound cl_35066 [cl_23709,cl_30984] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23709 v h) (hints_cons _ _ _ (der_30984 v h) (by intro d hd; cases hd)))
def cl_35068 : CNF.NClause := [(69,true),(27,true),(11,false),(9,false),(2,false)]
theorem der_35068 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35068 :=
  CNF.rup_sound cl_35068 [cl_30339,cl_30276] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30339 v h) (hints_cons _ _ _ (der_30276 v h) (by intro d hd; cases hd)))
def cl_35069 : CNF.NClause := [(54,false),(67,false),(89,true),(81,false),(83,false),(23,true),(65,false)]
theorem der_35069 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35069 :=
  CNF.rup_sound cl_35069 [cl_27004,cl_32580] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27004 v h) (hints_cons _ _ _ (der_32580 v h) (by intro d hd; cases hd)))
def cl_35070 : CNF.NClause := [(123,true),(41,true),(46,false),(36,false),(31,true),(56,true)]
theorem der_35070 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35070 :=
  CNF.rup_sound cl_35070 [cl_31651,cl_31653] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31651 v h) (hints_cons _ _ _ (der_31653 v h) (by intro d hd; cases hd)))
def cl_35071 : CNF.NClause := [(108,true),(48,true),(46,false),(49,false),(47,true),(61,true)]
theorem der_35071 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35071 :=
  CNF.rup_sound cl_35071 [cl_26146,cl_25833] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26146 v h) (hints_cons _ _ _ (der_25833 v h) (by intro d hd; cases hd)))
def cl_35072 : CNF.NClause := [(112,true),(54,true),(46,false),(40,false),(43,true)]
theorem der_35072 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35072 :=
  CNF.rup_sound cl_35072 [cl_31993,cl_31420] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31993 v h) (hints_cons _ _ _ (der_31420 v h) (by intro d hd; cases hd)))
def cl_35074 : CNF.NClause := [(74,true),(23,true),(29,false),(10,true),(6,false),(2,false)]
theorem der_35074 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35074 :=
  CNF.rup_sound cl_35074 [cl_30587,cl_30516] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30587 v h) (hints_cons _ _ _ (der_30516 v h) (by intro d hd; cases hd)))
def cl_35082 : CNF.NClause := [(67,true),(21,false),(22,false),(23,true)]
theorem der_35082 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35082 :=
  CNF.rup_sound cl_35082 [cl_29882,cl_29939] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29882 v h) (hints_cons _ _ _ (der_29939 v h) (by intro d hd; cases hd)))
def cl_35088 : CNF.NClause := [(115,true),(55,false),(36,false),(33,true)]
theorem der_35088 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35088 :=
  CNF.rup_sound cl_35088 [cl_31550,cl_31548] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31550 v h) (hints_cons _ _ _ (der_31548 v h) (by intro d hd; cases hd)))
def cl_35090 : CNF.NClause := [(48,false),(64,true),(83,false),(77,false),(88,false),(76,false)]
theorem der_35090 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35090 :=
  CNF.rup_sound cl_35090 [cl_27759,cl_33156] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27759 v h) (hints_cons _ _ _ (der_33156 v h) (by intro d hd; cases hd)))
def cl_35094 : CNF.NClause := [(71,true),(20,false),(13,false),(7,true),(1,true)]
theorem der_35094 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35094 :=
  CNF.rup_sound cl_35094 [cl_30332,cl_30333] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30332 v h) (hints_cons _ _ _ (der_30333 v h) (by intro d hd; cases hd)))
def cl_35099 : CNF.NClause := [(58,false),(89,true),(69,false),(27,true),(76,false),(78,false)]
theorem der_35099 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35099 :=
  CNF.rup_sound cl_35099 [cl_26916,cl_32508] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26916 v h) (hints_cons _ _ _ (der_32508 v h) (by intro d hd; cases hd)))
def cl_35103 : CNF.NClause := [(919,true),(920,true),(907,true),(923,true),(915,true),(922,true),(928,true),(916,true),(911,true),(906,true),(902,true),(900,true)]
theorem der_35103 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35103 :=
  CNF.rup_sound cl_35103 [cl_15674,cl_12659,cl_15669,cl_15694] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15674 v h) (hints_cons _ _ _ (inp_12659 v h) (hints_cons _ _ _ (der_15669 v h) (hints_cons _ _ _ (der_15694 v h) (by intro d hd; cases hd)))))
def cl_35106 : CNF.NClause := [(74,true),(23,true),(29,true),(10,true),(6,false),(2,false)]
theorem der_35106 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35106 :=
  CNF.rup_sound cl_35106 [cl_30519,cl_24465] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30519 v h) (hints_cons _ _ _ (der_24465 v h) (by intro d hd; cases hd)))
def cl_35111 : CNF.NClause := [(919,true),(920,true),(903,false),(921,true),(907,true),(923,true),(928,true),(926,true),(913,true),(911,true),(906,true)]
theorem der_35111 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35111 :=
  CNF.rup_sound cl_35111 [cl_15673,cl_12659,cl_15703] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15673 v h) (hints_cons _ _ _ (inp_12659 v h) (hints_cons _ _ _ (der_15703 v h) (by intro d hd; cases hd))))
def cl_35116 : CNF.NClause := [(37,false),(109,true),(35,false),(53,true)]
theorem der_35116 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35116 :=
  CNF.rup_sound cl_35116 [cl_30119,cl_30120] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30119 v h) (hints_cons _ _ _ (der_30120 v h) (by intro d hd; cases hd)))
def cl_35117 : CNF.NClause := [(109,true),(53,true),(35,false),(46,false)]
theorem der_35117 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35117 :=
  CNF.rup_sound cl_35117 [cl_30784,cl_30785,cl_35116] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30784 v h) (hints_cons _ _ _ (der_30785 v h) (hints_cons _ _ _ (der_35116 v h) (by intro d hd; cases hd))))
def cl_35118 : CNF.NClause := [(123,true),(46,false),(36,false),(31,true),(56,true)]
theorem der_35118 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35118 :=
  CNF.rup_sound cl_35118 [cl_31841,cl_35070] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31841 v h) (hints_cons _ _ _ (der_35070 v h) (by intro d hd; cases hd)))
def cl_35119 : CNF.NClause := [(88,true),(17,true),(13,false),(9,false)]
theorem der_35119 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35119 :=
  CNF.rup_sound cl_35119 [cl_30024,cl_29945] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30024 v h) (hints_cons _ _ _ (der_29945 v h) (by intro d hd; cases hd)))
def cl_35125 : CNF.NClause := [(74,true),(23,true),(2,false),(10,true),(6,false)]
theorem der_35125 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35125 :=
  CNF.rup_sound cl_35125 [cl_35074,cl_35106] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35074 v h) (hints_cons _ _ _ (der_35106 v h) (by intro d hd; cases hd)))
def cl_35134 : CNF.NClause := [(74,true),(23,false),(10,true),(6,false),(2,false)]
theorem der_35134 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35134 :=
  CNF.rup_sound cl_35134 [cl_30515,cl_30518] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30515 v h) (hints_cons _ _ _ (der_30518 v h) (by intro d hd; cases hd)))
def cl_35139 : CNF.NClause := [(108,true),(49,false),(47,true),(61,true),(46,false)]
theorem der_35139 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35139 :=
  CNF.rup_sound cl_35139 [cl_35071,cl_31590,cl_31880] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35071 v h) (hints_cons _ _ _ (der_31590 v h) (hints_cons _ _ _ (der_31880 v h) (by intro d hd; cases hd))))
def cl_35140 : CNF.NClause := [(88,true),(21,false),(17,false),(9,false)]
theorem der_35140 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35140 :=
  CNF.rup_sound cl_35140 [cl_29942,cl_29943] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29942 v h) (hints_cons _ _ _ (der_29943 v h) (by intro d hd; cases hd)))
def cl_35143 : CNF.NClause := [(83,true),(23,true),(17,false),(11,false),(4,false)]
theorem der_35143 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35143 :=
  CNF.rup_sound cl_35143 [cl_30343,cl_30609] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30343 v h) (hints_cons _ _ _ (der_30609 v h) (by intro d hd; cases hd)))
def cl_35149 : CNF.NClause := [(49,false),(86,true),(18,true),(69,false),(73,false),(77,false),(65,false)]
theorem der_35149 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35149 :=
  CNF.rup_sound cl_35149 [cl_34297,cl_34725] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34297 v h) (hints_cons _ _ _ (der_34725 v h) (by intro d hd; cases hd)))
def cl_35154 : CNF.NClause := [(70,true),(17,false),(14,true),(6,false),(3,true)]
theorem der_35154 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35154 :=
  CNF.rup_sound cl_35154 [cl_30475,cl_30479,cl_30474] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30475 v h) (hints_cons _ _ _ (der_30479 v h) (hints_cons _ _ _ (der_30474 v h) (by intro d hd; cases hd))))
def cl_35157 : CNF.NClause := [(49,false),(18,true),(73,false),(65,false),(69,false),(77,false)]
theorem der_35157 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35157 :=
  CNF.rup_sound cl_35157 [cl_26727,cl_34297,cl_34725] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26727 v h) (hints_cons _ _ _ (der_34297 v h) (hints_cons _ _ _ (der_34725 v h) (by intro d hd; cases hd))))
def cl_35158 : CNF.NClause := [(86,false),(120,false),(97,false),(108,false),(99,false),(47,false),(33,false),(84,false),(40,false),(34,true),(85,false),(64,false),(90,false),(75,false),(22,true),(83,false),(92,false),(82,false),(5,false)]
theorem der_35158 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35158 :=
  CNF.rup_sound cl_35158 [cl_34783,cl_4609,cl_31280,cl_35062,cl_7953] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34783 v h) (hints_cons _ _ _ (inp_4609 v h) (hints_cons _ _ _ (der_31280 v h) (hints_cons _ _ _ (der_35062 v h) (hints_cons _ _ _ (inp_7953 v h) (by intro d hd; cases hd))))))
def cl_35170 : CNF.NClause := [(111,true),(42,false),(38,true),(46,false)]
theorem der_35170 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35170 :=
  CNF.rup_sound cl_35170 [cl_31297,cl_31304] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31297 v h) (hints_cons _ _ _ (der_31304 v h) (by intro d hd; cases hd)))
def cl_35173 : CNF.NClause := [(107,true),(41,true),(58,true),(48,false),(39,false)]
theorem der_35173 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35173 :=
  CNF.rup_sound cl_35173 [cl_31966,cl_31969] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31966 v h) (hints_cons _ _ _ (der_31969 v h) (by intro d hd; cases hd)))
def cl_35176 : CNF.NClause := [(80,true),(15,false),(7,true),(11,false)]
theorem der_35176 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35176 :=
  CNF.rup_sound cl_35176 [cl_30382,cl_30506] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30382 v h) (hints_cons _ _ _ (der_30506 v h) (by intro d hd; cases hd)))
def cl_35178 : CNF.NClause := [(88,true),(21,true),(17,false),(9,false)]
theorem der_35178 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35178 :=
  CNF.rup_sound cl_35178 [cl_29942,cl_23260] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29942 v h) (hints_cons _ _ _ (der_23260 v h) (by intro d hd; cases hd)))
def cl_35184 : CNF.NClause := [(84,true),(16,false),(13,false),(5,false)]
theorem der_35184 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35184 :=
  CNF.rup_sound cl_35184 [cl_30378,cl_30509] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30378 v h) (hints_cons _ _ _ (der_30509 v h) (by intro d hd; cases hd)))
def cl_35187 : CNF.NClause := [(69,true),(27,false),(11,false),(9,false),(2,false)]
theorem der_35187 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35187 :=
  CNF.rup_sound cl_35187 [cl_34974,cl_30439] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34974 v h) (hints_cons _ _ _ (der_30439 v h) (by intro d hd; cases hd)))
def cl_35189 : CNF.NClause := [(99,true),(43,true),(47,false),(39,false)]
theorem der_35189 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35189 :=
  CNF.rup_sound cl_35189 [cl_31716,cl_31704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31716 v h) (hints_cons _ _ _ (der_31704 v h) (by intro d hd; cases hd)))
def cl_35192 : CNF.NClause := [(114,true),(36,true),(35,true),(42,false),(48,false),(54,true)]
theorem der_35192 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35192 :=
  CNF.rup_sound cl_35192 [cl_31767,cl_31778] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31767 v h) (hints_cons _ _ _ (der_31778 v h) (by intro d hd; cases hd)))
def cl_35194 : CNF.NClause := [(115,true),(36,false),(47,true),(33,false)]
theorem der_35194 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35194 :=
  CNF.rup_sound cl_35194 [cl_30116,cl_31573,cl_31888,cl_31567] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30116 v h) (hints_cons _ _ _ (der_31573 v h) (hints_cons _ _ _ (der_31888 v h) (hints_cons _ _ _ (der_31567 v h) (by intro d hd; cases hd)))))
def cl_35196 : CNF.NClause := [(86,true),(22,false),(14,true),(5,false),(1,true)]
theorem der_35196 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35196 :=
  CNF.rup_sound cl_35196 [cl_30321,cl_30323] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30321 v h) (hints_cons _ _ _ (der_30323 v h) (by intro d hd; cases hd)))
def cl_35199 : CNF.NClause := [(95,true),(48,false),(33,false),(38,true),(56,true)]
theorem der_35199 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35199 :=
  CNF.rup_sound cl_35199 [cl_31450,cl_31448] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31450 v h) (hints_cons _ _ _ (der_31448 v h) (by intro d hd; cases hd)))
def cl_35201 : CNF.NClause := [(91,true),(18,false),(6,false),(12,true)]
theorem der_35201 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35201 :=
  CNF.rup_sound cl_35201 [cl_35029,cl_35053] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35029 v h) (hints_cons _ _ _ (der_35053 v h) (by intro d hd; cases hd)))
def cl_35206 : CNF.NClause := [(91,true),(918,true),(901,true),(927,true),(18,true),(926,true),(922,true),(911,true),(909,true),(6,false)]
theorem der_35206 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35206 :=
  CNF.rup_sound cl_35206 [cl_15884,cl_29855,cl_29889,cl_15891,cl_15890,cl_15715,cl_15667,cl_12690] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15884 v h) (hints_cons _ _ _ (der_29855 v h) (hints_cons _ _ _ (der_29889 v h) (hints_cons _ _ _ (der_15891 v h) (hints_cons _ _ _ (der_15890 v h) (hints_cons _ _ _ (der_15715 v h) (hints_cons _ _ _ (der_15667 v h) (hints_cons _ _ _ (inp_12690 v h) (by intro d hd; cases hd)))))))))
def cl_35208 : CNF.NClause := [(116,true),(52,false),(34,true),(36,false)]
theorem der_35208 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35208 :=
  CNF.rup_sound cl_35208 [cl_31309,cl_31321] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31309 v h) (hints_cons _ _ _ (der_31321 v h) (by intro d hd; cases hd)))
def cl_35213 : CNF.NClause := [(106,true),(47,false),(34,true),(40,false)]
theorem der_35213 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35213 :=
  CNF.rup_sound cl_35213 [cl_31273,cl_31280] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31273 v h) (hints_cons _ _ _ (der_31280 v h) (by intro d hd; cases hd)))
def cl_35216 : CNF.NClause := [(67,true),(21,false),(23,false)]
theorem der_35216 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35216 :=
  CNF.rup_sound cl_35216 [cl_35028,cl_35055] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35028 v h) (hints_cons _ _ _ (der_35055 v h) (by intro d hd; cases hd)))
def cl_35218 : CNF.NClause := [(115,true),(36,true),(47,false),(33,false)]
theorem der_35218 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35218 :=
  CNF.rup_sound cl_35218 [cl_30843,cl_35065,cl_30844] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30843 v h) (hints_cons _ _ _ (der_35065 v h) (hints_cons _ _ _ (der_30844 v h) (by intro d hd; cases hd))))
def cl_35219 : CNF.NClause := [(115,true),(47,false),(33,false)]
theorem der_35219 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35219 :=
  CNF.rup_sound cl_35219 [cl_35062,cl_35218] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35062 v h) (hints_cons _ _ _ (der_35218 v h) (by intro d hd; cases hd)))
def cl_35222 : CNF.NClause := [(75,true),(16,false),(10,true),(9,false),(3,true)]
theorem der_35222 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35222 :=
  CNF.rup_sound cl_35222 [cl_35048,cl_30550,cl_24500] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35048 v h) (hints_cons _ _ _ (der_30550 v h) (hints_cons _ _ _ (der_24500 v h) (by intro d hd; cases hd))))
def cl_35226 : CNF.NClause := [(108,true),(48,false),(47,false),(46,false),(61,true)]
theorem der_35226 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35226 :=
  CNF.rup_sound cl_35226 [cl_35058,cl_31877] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35058 v h) (hints_cons _ _ _ (der_31877 v h) (by intro d hd; cases hd)))
def cl_35237 : CNF.NClause := [(115,true),(44,false),(55,false),(33,true),(47,true)]
theorem der_35237 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35237 :=
  CNF.rup_sound cl_35237 [cl_35088,cl_31549] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35088 v h) (hints_cons _ _ _ (der_31549 v h) (by intro d hd; cases hd)))
def cl_35238 : CNF.NClause := [(86,false),(108,false),(110,false),(67,false),(84,false),(112,false),(75,false),(111,false),(35,false),(31,true),(83,false),(46,false),(56,true),(85,false),(22,true),(78,false),(92,false),(82,false),(5,false)]
theorem der_35238 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35238 :=
  CNF.rup_sound cl_35238 [cl_34840,cl_4609,cl_35117,cl_35118,cl_7952] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34840 v h) (hints_cons _ _ _ (inp_4609 v h) (hints_cons _ _ _ (der_35117 v h) (hints_cons _ _ _ (der_35118 v h) (hints_cons _ _ _ (inp_7952 v h) (by intro d hd; cases hd))))))
def cl_35242 : CNF.NClause := [(71,true),(26,false),(13,false),(7,true),(1,true)]
theorem der_35242 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35242 :=
  CNF.rup_sound cl_35242 [cl_35094,cl_24185] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35094 v h) (hints_cons _ _ _ (der_24185 v h) (by intro d hd; cases hd)))
def cl_35244 : CNF.NClause := [(84,true),(16,true),(13,false),(5,false),(2,false)]
theorem der_35244 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35244 :=
  CNF.rup_sound cl_35244 [cl_30021,cl_30628] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30021 v h) (hints_cons _ _ _ (der_30628 v h) (by intro d hd; cases hd)))
def cl_35246 : CNF.NClause := [(67,true),(918,true),(917,true),(916,true),(21,false),(22,true),(926,true),(23,true),(913,true),(911,true),(909,true),(906,true),(902,true)]
theorem der_35246 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35246 :=
  CNF.rup_sound cl_35246 [cl_15888,cl_15889,cl_23479,cl_29939,cl_15890,cl_15886,cl_15675,cl_22745] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15888 v h) (hints_cons _ _ _ (der_15889 v h) (hints_cons _ _ _ (der_23479 v h) (hints_cons _ _ _ (der_29939 v h) (hints_cons _ _ _ (der_15890 v h) (hints_cons _ _ _ (der_15886 v h) (hints_cons _ _ _ (der_15675 v h) (hints_cons _ _ _ (der_22745 v h) (by intro d hd; cases hd)))))))))
def cl_35252 : CNF.NClause := [(97,true),(52,false),(42,false),(47,true),(56,true)]
theorem der_35252 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35252 :=
  CNF.rup_sound cl_35252 [cl_31915,cl_31916] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31915 v h) (hints_cons _ _ _ (der_31916 v h) (by intro d hd; cases hd)))
def cl_35255 : CNF.NClause := [(34,false),(75,true),(85,false),(80,false),(65,false),(87,false),(3,true)]
theorem der_35255 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35255 :=
  CNF.rup_sound cl_35255 [cl_27643,cl_33069] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27643 v h) (hints_cons _ _ _ (der_33069 v h) (by intro d hd; cases hd)))
def cl_35269 : CNF.NClause := [(73,true),(128,false),(21,true),(134,true),(7,true),(4,false)]
theorem der_35269 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35269 :=
  CNF.rup_sound cl_35269 [cl_15787,cl_15773,cl_30546,cl_30548,cl_15793,cl_15784,cl_8039] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15787 v h) (hints_cons _ _ _ (der_15773 v h) (hints_cons _ _ _ (der_30546 v h) (hints_cons _ _ _ (der_30548 v h) (hints_cons _ _ _ (der_15793 v h) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (inp_8039 v h) (by intro d hd; cases hd))))))))
def cl_35271 : CNF.NClause := [(70,true),(584,true),(562,true),(17,true),(579,true),(580,true),(581,true),(568,true),(570,true),(565,true),(14,true),(6,false),(3,true)]
theorem der_35271 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35271 :=
  CNF.rup_sound cl_35271 [cl_14202,cl_14189,cl_15836,cl_15834,cl_13749,cl_30477,cl_30474,cl_14205,cl_14213,cl_10603,cl_10623,cl_10640,cl_10750] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_14202 v h) (hints_cons _ _ _ (inp_14189 v h) (hints_cons _ _ _ (der_15836 v h) (hints_cons _ _ _ (der_15834 v h) (hints_cons _ _ _ (inp_13749 v h) (hints_cons _ _ _ (der_30477 v h) (hints_cons _ _ _ (der_30474 v h) (hints_cons _ _ _ (inp_14205 v h) (hints_cons _ _ _ (inp_14213 v h) (hints_cons _ _ _ (inp_10603 v h) (hints_cons _ _ _ (inp_10623 v h) (hints_cons _ _ _ (inp_10640 v h) (hints_cons _ _ _ (inp_10750 v h) (by intro d hd; cases hd))))))))))))))
def cl_35283 : CNF.NClause := [(88,true),(17,false),(9,false)]
theorem der_35283 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35283 :=
  CNF.rup_sound cl_35283 [cl_35178,cl_35140] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35178 v h) (hints_cons _ _ _ (der_35140 v h) (by intro d hd; cases hd)))
def cl_35284 : CNF.NClause := [(88,true),(13,false),(9,false)]
theorem der_35284 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35284 :=
  CNF.rup_sound cl_35284 [cl_35119,cl_35283] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35119 v h) (hints_cons _ _ _ (der_35283 v h) (by intro d hd; cases hd)))
def cl_35287 : CNF.NClause := [(104,true),(41,true),(35,false),(52,false),(38,true)]
theorem der_35287 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35287 :=
  CNF.rup_sound cl_35287 [cl_31723,cl_23834] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31723 v h) (hints_cons _ _ _ (der_23834 v h) (by intro d hd; cases hd)))
def cl_35295 : CNF.NClause := [(35,false),(109,true),(46,false),(58,true)]
theorem der_35295 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35295 :=
  CNF.rup_sound cl_35295 [cl_35117,cl_30968,cl_30781,cl_30782] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35117 v h) (hints_cons _ _ _ (der_30968 v h) (hints_cons _ _ _ (der_30781 v h) (hints_cons _ _ _ (der_30782 v h) (by intro d hd; cases hd)))))
def cl_35297 : CNF.NClause := [(52,false),(21,true),(88,false),(79,false),(66,false),(85,false)]
theorem der_35297 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35297 :=
  CNF.rup_sound cl_35297 [cl_26762,cl_34759,cl_34580] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26762 v h) (hints_cons _ _ _ (der_34759 v h) (hints_cons _ _ _ (der_34580 v h) (by intro d hd; cases hd))))
def cl_35307 : CNF.NClause := [(102,true),(32,true),(44,false),(50,false)]
theorem der_35307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35307 :=
  CNF.rup_sound cl_35307 [cl_31936,cl_31943] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31936 v h) (hints_cons _ _ _ (der_31943 v h) (by intro d hd; cases hd)))
def cl_35314 : CNF.NClause := [(109,true),(46,true),(58,true),(53,false),(35,false)]
theorem der_35314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35314 :=
  CNF.rup_sound cl_35314 [cl_31334,cl_30783] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31334 v h) (hints_cons _ _ _ (der_30783 v h) (by intro d hd; cases hd)))
def cl_35316 : CNF.NClause := [(121,true),(39,true),(53,false),(42,false),(31,true)]
theorem der_35316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35316 :=
  CNF.rup_sound cl_35316 [cl_31571,cl_31879] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31571 v h) (hints_cons _ _ _ (der_31879 v h) (by intro d hd; cases hd)))
def cl_35317 : CNF.NClause := [(117,true),(49,true),(53,false),(45,true),(36,false)]
theorem der_35317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35317 :=
  CNF.rup_sound cl_35317 [cl_32015,cl_30128] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32015 v h) (hints_cons _ _ _ (der_30128 v h) (by intro d hd; cases hd)))
def cl_35325 : CNF.NClause := [(36,true),(50,false),(52,false),(116,true)]
theorem der_35325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35325 :=
  CNF.rup_sound cl_35325 [cl_31318,cl_31307] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31318 v h) (hints_cons _ _ _ (der_31307 v h) (by intro d hd; cases hd)))
def cl_35327 : CNF.NClause := [(110,true),(39,false),(52,false),(33,true)]
theorem der_35327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35327 :=
  CNF.rup_sound cl_35327 [cl_31530,cl_31518] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31530 v h) (hints_cons _ _ _ (der_31518 v h) (by intro d hd; cases hd)))
def cl_35328 : CNF.NClause := [(119,true),(60,false),(52,false),(48,false),(40,true)]
theorem der_35328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35328 :=
  CNF.rup_sound cl_35328 [cl_25808,cl_31889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25808 v h) (hints_cons _ _ _ (der_31889 v h) (by intro d hd; cases hd)))
def cl_35329 : CNF.NClause := [(119,true),(60,false),(40,true),(52,false)]
theorem der_35329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35329 :=
  CNF.rup_sound cl_35329 [cl_31584,cl_35328] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31584 v h) (hints_cons _ _ _ (der_35328 v h) (by intro d hd; cases hd)))
def cl_35334 : CNF.NClause := [(77,true),(17,false),(16,true),(15,false)]
theorem der_35334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35334 :=
  CNF.rup_sound cl_35334 [cl_29929,cl_29859] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29929 v h) (hints_cons _ _ _ (der_29859 v h) (by intro d hd; cases hd)))
def cl_35336 : CNF.NClause := [(108,true),(47,true),(48,false),(46,false),(61,true)]
theorem der_35336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35336 :=
  CNF.rup_sound cl_35336 [cl_31877,cl_35139] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31877 v h) (hints_cons _ _ _ (der_35139 v h) (by intro d hd; cases hd)))
def cl_35342 : CNF.NClause := [(69,true),(11,false),(2,false),(9,false)]
theorem der_35342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35342 :=
  CNF.rup_sound cl_35342 [cl_35068,cl_35187] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35068 v h) (hints_cons _ _ _ (der_35187 v h) (by intro d hd; cases hd)))
def cl_35346 : CNF.NClause := [(52,false),(21,true),(88,false),(79,false),(66,false)]
theorem der_35346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35346 :=
  CNF.rup_sound cl_35346 [cl_35297,cl_32095,cl_34582] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35297 v h) (hints_cons _ _ _ (der_32095 v h) (hints_cons _ _ _ (der_34582 v h) (by intro d hd; cases hd))))
def cl_35356 : CNF.NClause := [(76,true),(27,false),(10,true),(8,false),(1,true)]
theorem der_35356 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35356 :=
  CNF.rup_sound cl_35356 [cl_30379,cl_30531] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30379 v h) (hints_cons _ _ _ (der_30531 v h) (by intro d hd; cases hd)))
def cl_35378 : CNF.NClause := [(96,true),(44,false),(39,false),(54,true),(56,true)]
theorem der_35378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35378 :=
  CNF.rup_sound cl_35378 [cl_25392,cl_31236] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25392 v h) (hints_cons _ _ _ (der_31236 v h) (by intro d hd; cases hd)))
def cl_35380 : CNF.NClause := [(36,false),(113,true),(40,true),(61,true),(38,true),(39,false)]
theorem der_35380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35380 :=
  CNF.rup_sound cl_35380 [cl_24831,cl_31142] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_24831 v h) (hints_cons _ _ _ (der_31142 v h) (by intro d hd; cases hd)))
def cl_35388 : CNF.NClause := [(119,true),(44,false),(48,false),(40,true),(31,true)]
theorem der_35388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35388 :=
  CNF.rup_sound cl_35388 [cl_26156,cl_31889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26156 v h) (hints_cons _ _ _ (der_31889 v h) (by intro d hd; cases hd)))
def cl_35392 : CNF.NClause := [(86,true),(22,true),(160,true),(14,true),(5,false),(1,true)]
theorem der_35392 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35392 :=
  CNF.rup_sound cl_35392 [cl_13817,cl_13809,cl_13736,cl_30317,cl_30323,cl_13824,cl_13813,cl_8303] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_13817 v h) (hints_cons _ _ _ (inp_13809 v h) (hints_cons _ _ _ (inp_13736 v h) (hints_cons _ _ _ (der_30317 v h) (hints_cons _ _ _ (der_30323 v h) (hints_cons _ _ _ (inp_13824 v h) (hints_cons _ _ _ (inp_13813 v h) (hints_cons _ _ _ (inp_8303 v h) (by intro d hd; cases hd)))))))))
def cl_35410 : CNF.NClause := [(94,true),(50,false),(40,true),(45,true),(35,false)]
theorem der_35410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35410 :=
  CNF.rup_sound cl_35410 [cl_23858,cl_31393] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23858 v h) (hints_cons _ _ _ (der_31393 v h) (by intro d hd; cases hd)))
def cl_35418 : CNF.NClause := [(113,true),(36,true),(40,false),(39,false),(38,true)]
theorem der_35418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35418 :=
  CNF.rup_sound cl_35418 [cl_30828,cl_30829] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30828 v h) (hints_cons _ _ _ (der_30829 v h) (by intro d hd; cases hd)))
def cl_35419 : CNF.NClause := [(33,true),(113,false),(121,false),(107,false),(51,true),(96,false),(81,false),(39,false),(35,false),(84,false),(68,false),(52,false),(79,false),(74,false),(72,false),(12,true),(69,false),(87,false),(2,false)]
theorem der_35419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35419 :=
  CNF.rup_sound cl_35419 [cl_4225,cl_35327,cl_33312,cl_7945,cl_31433] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4225 v h) (hints_cons _ _ _ (der_35327 v h) (hints_cons _ _ _ (der_33312 v h) (hints_cons _ _ _ (inp_7945 v h) (hints_cons _ _ _ (der_31433 v h) (by intro d hd; cases hd))))))
def cl_35421 : CNF.NClause := [(81,true),(23,false),(15,true),(9,false),(1,true)]
theorem der_35421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35421 :=
  CNF.rup_sound cl_35421 [cl_30406,cl_30407] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30406 v h) (hints_cons _ _ _ (der_30407 v h) (by intro d hd; cases hd)))
def cl_35435 : CNF.NClause := [(91,true),(26,false),(12,true),(6,false)]
theorem der_35435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35435 :=
  CNF.rup_sound cl_35435 [cl_29855,cl_35201] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29855 v h) (hints_cons _ _ _ (der_35201 v h) (by intro d hd; cases hd)))
def cl_35436 : CNF.NClause := [(36,false),(99,false),(110,false),(107,false),(92,false),(96,false),(75,false),(40,false),(38,true),(67,false),(42,false),(85,false),(39,false),(31,true),(78,false),(84,false),(22,true),(83,false),(82,false)]
theorem der_35436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35436 :=
  CNF.rup_sound cl_35436 [cl_34893,cl_30806,cl_34840,cl_7945,cl_30075] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34893 v h) (hints_cons _ _ _ (der_30806 v h) (hints_cons _ _ _ (der_34840 v h) (hints_cons _ _ _ (inp_7945 v h) (hints_cons _ _ _ (der_30075 v h) (by intro d hd; cases hd))))))
def cl_35437 : CNF.NClause := [(99,false),(110,false),(107,false),(92,false),(96,false),(75,false),(40,false),(38,true),(67,false),(42,false),(85,false),(39,false),(31,true),(78,false),(84,false),(22,true),(90,false),(83,false),(82,false),(5,false)]
theorem der_35437 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35437 :=
  CNF.rup_sound cl_35437 [cl_35436,cl_4609,cl_35418,cl_34785,cl_7945,cl_30075] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35436 v h) (hints_cons _ _ _ (inp_4609 v h) (hints_cons _ _ _ (der_35418 v h) (hints_cons _ _ _ (der_34785 v h) (hints_cons _ _ _ (inp_7945 v h) (hints_cons _ _ _ (der_30075 v h) (by intro d hd; cases hd)))))))
def cl_35438 : CNF.NClause := [(99,true),(43,true),(47,true),(35,false),(39,false)]
theorem der_35438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35438 :=
  CNF.rup_sound cl_35438 [cl_31433,cl_31431] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31433 v h) (hints_cons _ _ _ (der_31431 v h) (by intro d hd; cases hd)))
def cl_35444 : CNF.NClause := [(121,true),(42,false),(39,false),(31,true)]
theorem der_35444 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35444 :=
  CNF.rup_sound cl_35444 [cl_31878,cl_30075,cl_31570] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31878 v h) (hints_cons _ _ _ (der_30075 v h) (hints_cons _ _ _ (der_31570 v h) (by intro d hd; cases hd))))
def cl_35445 : CNF.NClause := [(107,true),(55,true),(39,false),(58,false)]
theorem der_35445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35445 :=
  CNF.rup_sound cl_35445 [cl_31957,cl_34992] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31957 v h) (hints_cons _ _ _ (der_34992 v h) (by intro d hd; cases hd)))
def cl_35449 : CNF.NClause := [(119,true),(44,false),(52,false),(40,true),(31,true)]
theorem der_35449 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35449 :=
  CNF.rup_sound cl_35449 [cl_35329,cl_26159] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35329 v h) (hints_cons _ _ _ (der_26159 v h) (by intro d hd; cases hd)))
def cl_35452 : CNF.NClause := [(104,true),(41,true),(35,false),(52,false)]
theorem der_35452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35452 :=
  CNF.rup_sound cl_35452 [cl_35287,cl_30101,cl_30102] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35287 v h) (hints_cons _ _ _ (der_30101 v h) (hints_cons _ _ _ (der_30102 v h) (by intro d hd; cases hd))))
def cl_35457 : CNF.NClause := [(119,true),(52,false),(44,false),(60,true),(40,false),(31,true)]
theorem der_35457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35457 :=
  CNF.rup_sound cl_35457 [cl_31892,cl_31891] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31892 v h) (hints_cons _ _ _ (der_31891 v h) (by intro d hd; cases hd)))
def cl_35468 : CNF.NClause := [(85,true),(27,false),(12,true),(5,false),(3,true)]
theorem der_35468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35468 :=
  CNF.rup_sound cl_35468 [cl_30487,cl_30491] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30487 v h) (hints_cons _ _ _ (der_30491 v h) (by intro d hd; cases hd)))
def cl_35469 : CNF.NClause := [(66,true),(16,true),(11,false),(6,false)]
theorem der_35469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35469 :=
  CNF.rup_sound cl_35469 [cl_29885,cl_29899] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29885 v h) (hints_cons _ _ _ (der_29899 v h) (by intro d hd; cases hd)))
def cl_35471 : CNF.NClause := [(79,true),(15,true),(14,true),(8,false),(2,false)]
theorem der_35471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35471 :=
  CNF.rup_sound cl_35471 [cl_30010,cl_29828] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30010 v h) (hints_cons _ _ _ (der_29828 v h) (by intro d hd; cases hd)))
def cl_35472 : CNF.NClause := [(55,false),(99,false),(114,false),(96,false),(109,false),(38,true),(121,false),(36,false),(34,true),(32,true),(45,true),(41,true),(40,true),(35,false),(52,false),(58,true),(39,false)]
theorem der_35472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35472 :=
  CNF.rup_sound cl_35472 [cl_35452,cl_31872,cl_31966,cl_7941,cl_31326,cl_31332,cl_35380,cl_35327,cl_7945] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35452 v h) (hints_cons _ _ _ (der_31872 v h) (hints_cons _ _ _ (der_31966 v h) (hints_cons _ _ _ (inp_7941 v h) (hints_cons _ _ _ (der_31326 v h) (hints_cons _ _ _ (der_31332 v h) (hints_cons _ _ _ (der_35380 v h) (hints_cons _ _ _ (der_35327 v h) (hints_cons _ _ _ (inp_7945 v h) (by intro d hd; cases hd))))))))))
def cl_35478 : CNF.NClause := [(110,true),(45,true),(52,false),(46,true),(39,false)]
theorem der_35478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35478 :=
  CNF.rup_sound cl_35478 [cl_25801,cl_35327] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25801 v h) (hints_cons _ _ _ (der_35327 v h) (by intro d hd; cases hd)))
def cl_35481 : CNF.NClause := [(96,true),(34,true),(44,false),(54,true),(39,false)]
theorem der_35481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35481 :=
  CNF.rup_sound cl_35481 [cl_35378,cl_31236,cl_25378] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35378 v h) (hints_cons _ _ _ (der_31236 v h) (hints_cons _ _ _ (der_25378 v h) (by intro d hd; cases hd))))
def cl_35483 : CNF.NClause := [(36,false),(114,true),(42,true),(54,true),(35,false)]
theorem der_35483 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35483 :=
  CNF.rup_sound cl_35483 [cl_31200,cl_31201] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31200 v h) (hints_cons _ _ _ (der_31201 v h) (by intro d hd; cases hd)))
def cl_35499 : CNF.NClause := [(99,true),(35,false),(39,false),(47,true)]
theorem der_35499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35499 :=
  CNF.rup_sound cl_35499 [cl_31849,cl_35438] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31849 v h) (hints_cons _ _ _ (der_35438 v h) (by intro d hd; cases hd)))
def cl_35510 : CNF.NClause := [(67,true),(24,true),(147,false),(146,true),(23,false)]
theorem der_35510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35510 :=
  CNF.rup_sound cl_35510 [cl_15790,cl_35216,cl_29938,cl_15787,cl_15786,cl_15642] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15790 v h) (hints_cons _ _ _ (der_35216 v h) (hints_cons _ _ _ (der_29938 v h) (hints_cons _ _ _ (der_15787 v h) (hints_cons _ _ _ (der_15786 v h) (hints_cons _ _ _ (der_15642 v h) (by intro d hd; cases hd)))))))
def cl_35511 : CNF.NClause := [(85,true),(916,true),(923,true),(926,true),(915,true),(921,true),(914,true),(913,true),(12,true),(909,true),(906,true),(5,false),(3,true)]
theorem der_35511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35511 :=
  CNF.rup_sound cl_35511 [cl_15702,cl_15878,cl_15869,cl_30491,cl_30493,cl_15887,cl_15885,cl_15676,cl_15683,cl_22745] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15702 v h) (hints_cons _ _ _ (der_15878 v h) (hints_cons _ _ _ (der_15869 v h) (hints_cons _ _ _ (der_30491 v h) (hints_cons _ _ _ (der_30493 v h) (hints_cons _ _ _ (der_15887 v h) (hints_cons _ _ _ (der_15885 v h) (hints_cons _ _ _ (der_15676 v h) (hints_cons _ _ _ (der_15683 v h) (hints_cons _ _ _ (der_22745 v h) (by intro d hd; cases hd)))))))))))
def cl_35514 : CNF.NClause := [(77,true),(19,false),(16,false)]
theorem der_35514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35514 :=
  CNF.rup_sound cl_35514 [cl_29810,cl_29896] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29810 v h) (hints_cons _ _ _ (der_29896 v h) (by intro d hd; cases hd)))
def cl_35516 : CNF.NClause := [(80,true),(24,false),(15,true),(11,false),(7,true)]
theorem der_35516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35516 :=
  CNF.rup_sound cl_35516 [cl_30414,cl_30415] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30414 v h) (hints_cons _ _ _ (der_30415 v h) (by intro d hd; cases hd)))
def cl_35518 : CNF.NClause := [(107,true),(41,true),(55,false),(39,false)]
theorem der_35518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35518 :=
  CNF.rup_sound cl_35518 [cl_34992,cl_31966] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34992 v h) (hints_cons _ _ _ (der_31966 v h) (by intro d hd; cases hd)))
def cl_35520 : CNF.NClause := [(112,true),(46,true),(43,true),(54,false),(40,false)]
theorem der_35520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35520 :=
  CNF.rup_sound cl_35520 [cl_31990,cl_31976] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31990 v h) (hints_cons _ _ _ (der_31976 v h) (by intro d hd; cases hd)))
def cl_35522 : CNF.NClause := [(41,false),(92,true),(74,false),(72,false),(76,false),(75,false)]
theorem der_35522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35522 :=
  CNF.rup_sound cl_35522 [cl_28398,cl_33650] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28398 v h) (hints_cons _ _ _ (der_33650 v h) (by intro d hd; cases hd)))
def cl_35525 : CNF.NClause := [(115,false),(122,false),(98,false),(48,true),(107,false),(35,false),(97,false),(106,false),(120,false),(99,false),(47,false),(46,true),(111,false),(55,false),(40,false)]
theorem der_35525 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35525 :=
  CNF.rup_sound cl_35525 [cl_7953,cl_7961,cl_31168,cl_31863] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_7953 v h) (hints_cons _ _ _ (inp_7961 v h) (hints_cons _ _ _ (der_31168 v h) (hints_cons _ _ _ (der_31863 v h) (by intro d hd; cases hd)))))
def cl_35526 : CNF.NClause := [(115,true),(33,true),(55,false),(47,false)]
theorem der_35526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35526 :=
  CNF.rup_sound cl_35526 [cl_31547,cl_35088] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31547 v h) (hints_cons _ _ _ (der_35088 v h) (by intro d hd; cases hd)))
def cl_35535 : CNF.NClause := [(21,false),(52,true),(67,false),(85,false),(66,false),(79,false),(88,false),(10,true),(7,true),(4,false)]
theorem der_35535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35535 :=
  CNF.rup_sound cl_35535 [cl_30547,cl_6657] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30547 v h) (hints_cons _ _ _ (inp_6657 v h) (by intro d hd; cases hd)))
def cl_35536 : CNF.NClause := [(93,true),(59,false),(60,false),(58,false)]
theorem der_35536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35536 :=
  CNF.rup_sound cl_35536 [cl_31788,cl_31781] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31788 v h) (hints_cons _ _ _ (der_31781 v h) (by intro d hd; cases hd)))
def cl_35537 : CNF.NClause := [(93,true),(57,true),(60,false),(58,false)]
theorem der_35537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35537 :=
  CNF.rup_sound cl_35537 [cl_31790,cl_35536] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31790 v h) (hints_cons _ _ _ (der_35536 v h) (by intro d hd; cases hd)))
def cl_35542 : CNF.NClause := [(119,true),(60,true),(52,true),(44,false),(31,true),(40,false)]
theorem der_35542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35542 :=
  CNF.rup_sound cl_35542 [cl_31893,cl_31894] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31893 v h) (hints_cons _ _ _ (der_31894 v h) (by intro d hd; cases hd)))
def cl_35543 : CNF.NClause := [(38,false),(73,false),(80,true),(71,false),(89,false),(82,false),(7,true)]
theorem der_35543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35543 :=
  CNF.rup_sound cl_35543 [cl_28118,cl_33438] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_28118 v h) (hints_cons _ _ _ (der_33438 v h) (by intro d hd; cases hd)))
def cl_35545 : CNF.NClause := [(77,true),(18,false),(16,false),(15,true)]
theorem der_35545 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35545 :=
  CNF.rup_sound cl_35545 [cl_29898,cl_29897] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29898 v h) (hints_cons _ _ _ (der_29897 v h) (by intro d hd; cases hd)))
def cl_35551 : CNF.NClause := [(43,false),(85,false),(81,false),(12,true),(72,false),(68,false)]
theorem der_35551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35551 :=
  CNF.rup_sound cl_35551 [cl_27925,cl_33312] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27925 v h) (hints_cons _ _ _ (der_33312 v h) (by intro d hd; cases hd)))
def cl_35555 : CNF.NClause := [(58,false),(113,false),(106,false),(99,false),(94,false),(121,false),(49,true),(112,false),(46,true),(60,true),(96,false),(42,true),(55,true),(44,false),(45,true),(31,true),(39,false),(40,false)]
theorem der_35555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35555 :=
  CNF.rup_sound cl_35555 [cl_35445,cl_31483,cl_7945,cl_7946,cl_35478,cl_31893,cl_31894] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35445 v h) (hints_cons _ _ _ (der_31483 v h) (hints_cons _ _ _ (inp_7945 v h) (hints_cons _ _ _ (inp_7946 v h) (hints_cons _ _ _ (der_35478 v h) (hints_cons _ _ _ (der_31893 v h) (hints_cons _ _ _ (der_31894 v h) (by intro d hd; cases hd))))))))
def cl_35559 : CNF.NClause := [(99,true),(60,false),(43,true),(39,false)]
theorem der_35559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35559 :=
  CNF.rup_sound cl_35559 [cl_35189,cl_31707] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35189 v h) (hints_cons _ _ _ (der_31707 v h) (by intro d hd; cases hd)))
def cl_35561 : CNF.NClause := [(28,false),(59,true),(62,false),(73,false),(20,true),(84,false),(81,false),(90,false),(6,false),(3,true)]
theorem der_35561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35561 :=
  CNF.rup_sound cl_35561 [cl_30474,cl_7553] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30474 v h) (hints_cons _ _ _ (inp_7553 v h) (by intro d hd; cases hd)))
def cl_35569 : CNF.NClause := [(91,true),(24,false),(12,true),(6,false)]
theorem der_35569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35569 :=
  CNF.rup_sound cl_35569 [cl_35201,cl_29889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35201 v h) (hints_cons _ _ _ (der_29889 v h) (by intro d hd; cases hd)))
def cl_35577 : CNF.NClause := [(67,true),(24,false),(23,false)]
theorem der_35577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35577 :=
  CNF.rup_sound cl_35577 [cl_35216,cl_29878] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35216 v h) (hints_cons _ _ _ (der_29878 v h) (by intro d hd; cases hd)))
def cl_35581 : CNF.NClause := [(43,false),(91,false),(68,false),(81,false),(72,false),(12,true)]
theorem der_35581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35581 :=
  CNF.rup_sound cl_35581 [cl_33262,cl_33273] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33262 v h) (hints_cons _ _ _ (der_33273 v h) (by intro d hd; cases hd)))
def cl_35584 : CNF.NClause := [(108,true),(46,true),(47,false),(48,false)]
theorem der_35584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35584 :=
  CNF.rup_sound cl_35584 [cl_31171,cl_31166,cl_31169] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31171 v h) (hints_cons _ _ _ (der_31166 v h) (hints_cons _ _ _ (der_31169 v h) (by intro d hd; cases hd))))
def cl_35585 : CNF.NClause := [(108,true),(61,true),(47,false),(48,false)]
theorem der_35585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35585 :=
  CNF.rup_sound cl_35585 [cl_35226,cl_35584] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35226 v h) (hints_cons _ _ _ (der_35584 v h) (by intro d hd; cases hd)))
def cl_35586 : CNF.NClause := [(97,true),(42,false),(56,true),(47,false)]
theorem der_35586 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35586 :=
  CNF.rup_sound cl_35586 [cl_35043,cl_31919] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35043 v h) (hints_cons _ _ _ (der_31919 v h) (by intro d hd; cases hd)))
def cl_35593 : CNF.NClause := [(93,true),(57,false),(61,true),(59,false),(60,false)]
theorem der_35593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35593 :=
  CNF.rup_sound cl_35593 [cl_25044,cl_31368] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_25044 v h) (hints_cons _ _ _ (der_31368 v h) (by intro d hd; cases hd)))
def cl_35596 : CNF.NClause := [(96,true),(44,false),(54,false),(34,true),(39,true)]
theorem der_35596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35596 :=
  CNF.rup_sound cl_35596 [cl_31221,cl_31232] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31221 v h) (hints_cons _ _ _ (der_31232 v h) (by intro d hd; cases hd)))
def cl_35599 : CNF.NClause := [(46,false),(77,false),(80,false),(78,false),(81,false),(79,false),(15,true)]
theorem der_35599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35599 :=
  CNF.rup_sound cl_35599 [cl_34875,cl_27459] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34875 v h) (hints_cons _ _ _ (der_27459 v h) (by intro d hd; cases hd)))
def cl_35600 : CNF.NClause := [(114,true),(35,false),(54,false),(42,false)]
theorem der_35600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35600 :=
  CNF.rup_sound cl_35600 [cl_30860,cl_31792,cl_31806] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30860 v h) (hints_cons _ _ _ (der_31792 v h) (hints_cons _ _ _ (der_31806 v h) (by intro d hd; cases hd))))
def cl_35607 : CNF.NClause := [(77,true),(130,false),(137,true),(153,true),(132,true),(126,true),(17,true),(16,false),(134,true),(127,true)]
theorem der_35607 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35607 :=
  CNF.rup_sound cl_35607 [cl_35514,cl_29897,cl_15785,cl_15784,cl_8044,cl_15631] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35514 v h) (hints_cons _ _ _ (der_29897 v h) (hints_cons _ _ _ (der_15785 v h) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (inp_8044 v h) (hints_cons _ _ _ (der_15631 v h) (by intro d hd; cases hd)))))))
def cl_35608 : CNF.NClause := [(55,false),(67,false),(80,true),(24,true),(76,true),(84,false),(63,false)]
theorem der_35608 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35608 :=
  CNF.rup_sound cl_35608 [cl_32815,cl_32888] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32815 v h) (hints_cons _ _ _ (der_32888 v h) (by intro d hd; cases hd)))
def cl_35610 : CNF.NClause := [(114,true),(35,false),(42,true),(54,false)]
theorem der_35610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35610 :=
  CNF.rup_sound cl_35610 [cl_31199,cl_31198] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31199 v h) (hints_cons _ _ _ (der_31198 v h) (by intro d hd; cases hd)))
def cl_35619 : CNF.NClause := [(113,true),(38,true),(39,false),(40,false)]
theorem der_35619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35619 :=
  CNF.rup_sound cl_35619 [cl_30806,cl_35418] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30806 v h) (hints_cons _ _ _ (der_35418 v h) (by intro d hd; cases hd)))
def cl_35623 : CNF.NClause := [(41,false),(76,false),(75,false),(74,false),(72,false),(10,true)]
theorem der_35623 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35623 :=
  CNF.rup_sound cl_35623 [cl_35522,cl_33650,cl_28340] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35522 v h) (hints_cons _ _ _ (der_33650 v h) (hints_cons _ _ _ (der_28340 v h) (by intro d hd; cases hd))))
def cl_35626 : CNF.NClause := [(46,false),(80,false),(81,false),(15,true),(79,false),(78,false)]
theorem der_35626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35626 :=
  CNF.rup_sound cl_35626 [cl_34875,cl_32933,cl_32934] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34875 v h) (hints_cons _ _ _ (der_32933 v h) (hints_cons _ _ _ (der_32934 v h) (by intro d hd; cases hd))))
def cl_35627 : CNF.NClause := [(96,true),(54,false),(34,true),(39,false)]
theorem der_35627 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35627 :=
  CNF.rup_sound cl_35627 [cl_31231,cl_31233] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31231 v h) (hints_cons _ _ _ (der_31233 v h) (by intro d hd; cases hd)))
def cl_35629 : CNF.NClause := [(67,true),(22,false),(23,false)]
theorem der_35629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35629 :=
  CNF.rup_sound cl_35629 [cl_29797,cl_29940] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29797 v h) (hints_cons _ _ _ (der_29940 v h) (by intro d hd; cases hd)))
def cl_35631 : CNF.NClause := [(37,false),(44,false),(35,false),(109,true)]
theorem der_35631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35631 :=
  CNF.rup_sound cl_35631 [cl_31883,cl_31334,cl_31887] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31883 v h) (hints_cons _ _ _ (der_31334 v h) (hints_cons _ _ _ (der_31887 v h) (by intro d hd; cases hd))))
def cl_35632 : CNF.NClause := [(44,false),(35,false),(53,false),(109,true)]
theorem der_35632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35632 :=
  CNF.rup_sound cl_35632 [cl_30782,cl_35631] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30782 v h) (hints_cons _ _ _ (der_35631 v h) (by intro d hd; cases hd)))
def cl_35633 : CNF.NClause := [(44,true),(35,false),(53,false),(109,true)]
theorem der_35633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35633 :=
  CNF.rup_sound cl_35633 [cl_30781,cl_35314,cl_31753,cl_24791] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30781 v h) (hints_cons _ _ _ (der_35314 v h) (hints_cons _ _ _ (der_31753 v h) (hints_cons _ _ _ (der_24791 v h) (by intro d hd; cases hd)))))
def cl_35634 : CNF.NClause := [(35,false),(109,true),(53,false)]
theorem der_35634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35634 :=
  CNF.rup_sound cl_35634 [cl_35632,cl_35633] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35632 v h) (hints_cons _ _ _ (der_35633 v h) (by intro d hd; cases hd)))
def cl_35636 : CNF.NClause := [(119,true),(44,false),(52,true),(31,true),(40,false)]
theorem der_35636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35636 :=
  CNF.rup_sound cl_35636 [cl_31893,cl_31890,cl_31894] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31893 v h) (hints_cons _ _ _ (der_31890 v h) (hints_cons _ _ _ (der_31894 v h) (by intro d hd; cases hd))))
def cl_35640 : CNF.NClause := [(121,true),(42,false),(39,false),(53,false)]
theorem der_35640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35640 :=
  CNF.rup_sound cl_35640 [cl_31075,cl_35444] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31075 v h) (hints_cons _ _ _ (der_35444 v h) (by intro d hd; cases hd)))
def cl_35642 : CNF.NClause := [(17,true),(917,true),(51,true),(920,true),(71,false),(926,true),(68,false),(915,true),(67,false),(914,true),(14,true),(911,true),(69,false),(909,true),(906,true),(6,false),(5,false),(902,true)]
theorem der_35642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35642 :=
  CNF.rup_sound cl_35642 [cl_15880,cl_15702,cl_15883,cl_15682,cl_22745,cl_15886,cl_29838,cl_30477,cl_6529] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15880 v h) (hints_cons _ _ _ (der_15702 v h) (hints_cons _ _ _ (der_15883 v h) (hints_cons _ _ _ (der_15682 v h) (hints_cons _ _ _ (der_22745 v h) (hints_cons _ _ _ (der_15886 v h) (hints_cons _ _ _ (der_29838 v h) (hints_cons _ _ _ (der_30477 v h) (hints_cons _ _ _ (inp_6529 v h) (by intro d hd; cases hd))))))))))
def cl_35643 : CNF.NClause := [(114,true),(48,false),(54,true),(42,false)]
theorem der_35643 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35643 :=
  CNF.rup_sound cl_35643 [cl_31778,cl_31765] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31778 v h) (hints_cons _ _ _ (der_31765 v h) (by intro d hd; cases hd)))
def cl_35646 : CNF.NClause := [(24,false),(55,true),(80,false),(76,false),(84,false),(67,false),(63,false),(12,true),(6,false)]
theorem der_35646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35646 :=
  CNF.rup_sound cl_35646 [cl_35569,cl_7041] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35569 v h) (hints_cons _ _ _ (inp_7041 v h) (by intro d hd; cases hd)))
def cl_35655 : CNF.NClause := [(73,true),(130,true),(21,true),(148,true),(153,true),(151,true),(136,true),(7,true),(4,false)]
theorem der_35655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35655 :=
  CNF.rup_sound cl_35655 [cl_30546,cl_30548,cl_15793,cl_15784,cl_15620,cl_15665] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30546 v h) (hints_cons _ _ _ (der_30548 v h) (hints_cons _ _ _ (der_15793 v h) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (der_15620 v h) (hints_cons _ _ _ (der_15665 v h) (by intro d hd; cases hd)))))))
def cl_35658 : CNF.NClause := [(114,true),(35,false),(42,false),(54,true)]
theorem der_35658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35658 :=
  CNF.rup_sound cl_35658 [cl_35643,cl_31780,cl_30864] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35643 v h) (hints_cons _ _ _ (der_31780 v h) (hints_cons _ _ _ (der_30864 v h) (by intro d hd; cases hd))))
def cl_35662 : CNF.NClause := [(18,false),(19,false),(49,true),(73,false),(17,true),(86,false),(15,true),(65,false),(12,true),(69,false),(6,false)]
theorem der_35662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35662 :=
  CNF.rup_sound cl_35662 [cl_35201,cl_23450,cl_6273] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35201 v h) (hints_cons _ _ _ (der_23450 v h) (hints_cons _ _ _ (inp_6273 v h) (by intro d hd; cases hd))))
def cl_35670 : CNF.NClause := [(99,true),(35,false),(39,false),(43,true)]
theorem der_35670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35670 :=
  CNF.rup_sound cl_35670 [cl_35189,cl_35499] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35189 v h) (hints_cons _ _ _ (der_35499 v h) (by intro d hd; cases hd)))
def cl_35672 : CNF.NClause := [(107,true),(80,false),(41,true),(39,false),(85,false),(76,false),(89,false),(27,false),(84,false),(67,false),(78,false),(15,true),(63,false),(12,true),(69,false),(7,true),(6,false),(3,true)]
theorem der_35672 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35672 :=
  CNF.rup_sound cl_35672 [cl_35518,cl_34992,cl_35646,cl_7425,cl_33152,cl_29833] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35518 v h) (hints_cons _ _ _ (der_34992 v h) (hints_cons _ _ _ (der_35646 v h) (hints_cons _ _ _ (inp_7425 v h) (hints_cons _ _ _ (der_33152 v h) (hints_cons _ _ _ (der_29833 v h) (by intro d hd; cases hd)))))))
def cl_35679 : CNF.NClause := [(77,true),(128,true),(145,true),(137,true),(148,true),(153,true),(16,false),(15,true),(138,true)]
theorem der_35679 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35679 :=
  CNF.rup_sound cl_35679 [cl_35514,cl_29898,cl_15785,cl_15783,cl_15624,cl_15662] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35514 v h) (hints_cons _ _ _ (der_29898 v h) (hints_cons _ _ _ (der_15785 v h) (hints_cons _ _ _ (der_15783 v h) (hints_cons _ _ _ (der_15624 v h) (hints_cons _ _ _ (der_15662 v h) (by intro d hd; cases hd)))))))
def cl_35692 : CNF.NClause := [(77,true),(132,true),(17,true),(137,true),(151,true),(16,false),(139,true),(138,true),(131,true),(127,true)]
theorem der_35692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35692 :=
  CNF.rup_sound cl_35692 [cl_15783,cl_35514,cl_29897,cl_15785,cl_15784,cl_15654,cl_15631,cl_15663] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15783 v h) (hints_cons _ _ _ (der_35514 v h) (hints_cons _ _ _ (der_29897 v h) (hints_cons _ _ _ (der_15785 v h) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (der_15654 v h) (hints_cons _ _ _ (der_15631 v h) (hints_cons _ _ _ (der_15663 v h) (by intro d hd; cases hd)))))))))
def cl_35694 : CNF.NClause := [(98,true),(52,true),(61,true),(55,true),(54,false),(53,false)]
theorem der_35694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35694 :=
  CNF.rup_sound cl_35694 [cl_30109,cl_31829] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30109 v h) (hints_cons _ _ _ (der_31829 v h) (by intro d hd; cases hd)))
def cl_35699 : CNF.NClause := [(36,false),(47,true),(98,false),(119,false),(104,false),(110,false),(52,false),(34,true),(42,false),(85,false),(66,false),(84,false),(83,false),(63,false),(65,false),(82,false),(5,false)]
theorem der_35699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35699 :=
  CNF.rup_sound cl_35699 [cl_26695,cl_35208,cl_31346,cl_7958,cl_35252] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26695 v h) (hints_cons _ _ _ (der_35208 v h) (hints_cons _ _ _ (der_31346 v h) (hints_cons _ _ _ (inp_7958 v h) (hints_cons _ _ _ (der_35252 v h) (by intro d hd; cases hd))))))
def cl_35701 : CNF.NClause := [(47,false),(75,true),(89,true),(66,false),(84,false),(68,false)]
theorem der_35701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35701 :=
  CNF.rup_sound cl_35701 [cl_34666,cl_34667] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_34666 v h) (hints_cons _ _ _ (der_34667 v h) (by intro d hd; cases hd)))
def cl_35707 : CNF.NClause := [(41,false),(75,true),(72,false),(76,false),(74,false)]
theorem der_35707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35707 :=
  CNF.rup_sound cl_35707 [cl_33660,cl_33664] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_33660 v h) (hints_cons _ _ _ (der_33664 v h) (by intro d hd; cases hd)))
def cl_35709 : CNF.NClause := [(21,false),(1071,true),(67,true),(1082,true),(1063,true),(22,true),(1081,true),(23,true),(1069,true),(1068,true),(1064,true),(1061,true),(1057,true),(1055,true)]
theorem der_35709 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35709 :=
  CNF.rup_sound cl_35709 [cl_23479,cl_29939,cl_15930,cl_15926,cl_13636,cl_15766,cl_22079] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23479 v h) (hints_cons _ _ _ (der_29939 v h) (hints_cons _ _ _ (der_15930 v h) (hints_cons _ _ _ (der_15926 v h) (hints_cons _ _ _ (inp_13636 v h) (hints_cons _ _ _ (der_15766 v h) (hints_cons _ _ _ (der_22079 v h) (by intro d hd; cases hd))))))))
def cl_35718 : CNF.NClause := [(115,true),(33,false),(44,false),(47,true)]
theorem der_35718 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35718 :=
  CNF.rup_sound cl_35718 [cl_35194,cl_30845,cl_31549] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35194 v h) (hints_cons _ _ _ (der_30845 v h) (hints_cons _ _ _ (der_31549 v h) (by intro d hd; cases hd))))
def cl_35719 : CNF.NClause := [(119,true),(44,false),(60,false),(40,true)]
theorem der_35719 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35719 :=
  CNF.rup_sound cl_35719 [cl_31895,cl_31889] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31895 v h) (hints_cons _ _ _ (der_31889 v h) (by intro d hd; cases hd)))
def cl_35724 : CNF.NClause := [(121,true),(53,true),(42,false),(39,false)]
theorem der_35724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35724 :=
  CNF.rup_sound cl_35724 [cl_35444,cl_31079,cl_31083] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35444 v h) (hints_cons _ _ _ (der_31079 v h) (hints_cons _ _ _ (der_31083 v h) (by intro d hd; cases hd))))
def cl_35728 : CNF.NClause := [(73,true),(28,false),(10,true),(7,true),(4,false)]
theorem der_35728 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35728 :=
  CNF.rup_sound cl_35728 [cl_30547,cl_30546] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30547 v h) (hints_cons _ _ _ (der_30546 v h) (by intro d hd; cases hd)))
def cl_35733 : CNF.NClause := [(21,true),(24,true),(67,false),(22,true),(23,true)]
theorem der_35733 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35733 :=
  CNF.rup_sound cl_35733 [cl_15930,cl_15928,cl_15929,cl_15927,cl_15173,cl_15738,cl_15926] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15930 v h) (hints_cons _ _ _ (der_15928 v h) (hints_cons _ _ _ (der_15929 v h) (hints_cons _ _ _ (der_15927 v h) (hints_cons _ _ _ (der_15173 v h) (hints_cons _ _ _ (der_15738 v h) (hints_cons _ _ _ (der_15926 v h) (by intro d hd; cases hd))))))))
def cl_35739 : CNF.NClause := [(109,true),(35,false),(44,false),(58,true)]
theorem der_35739 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35739 :=
  CNF.rup_sound cl_35739 [cl_30786,cl_35634] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30786 v h) (hints_cons _ _ _ (der_35634 v h) (by intro d hd; cases hd)))
def cl_35745 : CNF.NClause := [(52,false),(60,false),(114,false),(118,false),(109,false),(99,false),(35,false),(103,false),(121,false),(100,false),(38,true),(42,false),(40,true),(45,true),(41,true),(47,true),(56,true)]
theorem der_35745 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35745 :=
  CNF.rup_sound cl_35745 [cl_35452,cl_35252,cl_7941,cl_7948,cl_31872,cl_31290,cl_31294] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35452 v h) (hints_cons _ _ _ (der_35252 v h) (hints_cons _ _ _ (inp_7941 v h) (hints_cons _ _ _ (inp_7948 v h) (hints_cons _ _ _ (der_31872 v h) (hints_cons _ _ _ (der_31290 v h) (hints_cons _ _ _ (der_31294 v h) (by intro d hd; cases hd))))))))
def cl_35747 : CNF.NClause := [(20,false),(70,true),(6,false),(14,true)]
theorem der_35747 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35747 :=
  CNF.rup_sound cl_35747 [cl_30475,cl_30477] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30475 v h) (hints_cons _ _ _ (der_30477 v h) (by intro d hd; cases hd)))
def cl_35748 : CNF.NClause := [(20,false),(51,true),(71,false),(67,false),(68,false),(14,true),(69,false),(6,false),(5,false)]
theorem der_35748 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35748 :=
  CNF.rup_sound cl_35748 [cl_29838,cl_6529,cl_35747] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29838 v h) (hints_cons _ _ _ (inp_6529 v h) (hints_cons _ _ _ (der_35747 v h) (by intro d hd; cases hd))))
def cl_35752 : CNF.NClause := [(109,true),(35,true),(44,false),(53,false),(58,true)]
theorem der_35752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35752 :=
  CNF.rup_sound cl_35752 [cl_31752,cl_31751] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_31752 v h) (hints_cons _ _ _ (der_31751 v h) (by intro d hd; cases hd)))
def cl_35755 : CNF.NClause := [(62,true),(152,true),(151,false)]
theorem der_35755 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35755 :=
  CNF.rup_sound cl_35755 [cl_15792,cl_29833,cl_29837,cl_15794,cl_15791,cl_15619] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15792 v h) (hints_cons _ _ _ (der_29833 v h) (hints_cons _ _ _ (der_29837 v h) (hints_cons _ _ _ (der_15794 v h) (hints_cons _ _ _ (der_15791 v h) (hints_cons _ _ _ (der_15619 v h) (by intro d hd; cases hd)))))))
def cl_35776 : CNF.NClause := [(62,true),(133,true),(152,true),(27,false),(146,true),(147,true),(138,true),(134,true),(131,true),(127,true)]
theorem der_35776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35776 :=
  CNF.rup_sound cl_35776 [cl_29837,cl_35755,cl_15791,cl_15663,cl_8048] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29837 v h) (hints_cons _ _ _ (der_35755 v h) (hints_cons _ _ _ (der_15791 v h) (hints_cons _ _ _ (der_15663 v h) (hints_cons _ _ _ (inp_8048 v h) (by intro d hd; cases hd))))))
def cl_35784 : CNF.NClause := [(26,false),(57,true),(62,false),(71,false),(75,false),(83,false),(79,false),(12,true),(6,false)]
theorem der_35784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35784 :=
  CNF.rup_sound cl_35784 [cl_35435,cl_7297] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35435 v h) (hints_cons _ _ _ (inp_7297 v h) (by intro d hd; cases hd)))
def cl_35787 : CNF.NClause := [(234,true),(228,true),(222,true),(243,true),(239,true),(240,true),(229,true),(224,true),(218,true),(247,true),(242,true),(217,true),(220,false)]
theorem der_35787 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35787 :=
  CNF.rup_sound cl_35787 [cl_8543,cl_8657,cl_8678] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_8543 v h) (hints_cons _ _ _ (inp_8657 v h) (hints_cons _ _ _ (inp_8678 v h) (by intro d hd; cases hd))))
def cl_35794 : CNF.NClause := [(62,true),(28,false),(1070,true),(1081,true),(1076,true),(1077,true),(1069,true),(1066,true),(1064,true),(1057,true),(1055,true)]
theorem der_35794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35794 :=
  CNF.rup_sound cl_35794 [cl_29836,cl_29853,cl_15931,cl_15934,cl_13630,cl_15717,cl_13662] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29836 v h) (hints_cons _ _ _ (der_29853 v h) (hints_cons _ _ _ (der_15931 v h) (hints_cons _ _ _ (der_15934 v h) (hints_cons _ _ _ (inp_13630 v h) (hints_cons _ _ _ (der_15717 v h) (hints_cons _ _ _ (inp_13662 v h) (by intro d hd; cases hd))))))))
def cl_35797 : CNF.NClause := [(54,false),(81,true),(89,true),(74,false),(23,true),(83,false),(65,false)]
theorem der_35797 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35797 :=
  CNF.rup_sound cl_35797 [cl_32585,cl_32591] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32585 v h) (hints_cons _ _ _ (der_32591 v h) (by intro d hd; cases hd)))
def cl_35803 : CNF.NClause := [(67,true),(20,false),(24,false),(22,true),(23,true)]
theorem der_35803 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35803 :=
  CNF.rup_sound cl_35803 [cl_23479,cl_23253] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_23479 v h) (hints_cons _ _ _ (der_23253 v h) (by intro d hd; cases hd)))
def cl_35805 : CNF.NClause := [(114,true),(57,false),(54,true),(36,true),(42,false)]
theorem der_35805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35805 :=
  CNF.rup_sound cl_35805 [cl_35643,cl_31769] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35643 v h) (hints_cons _ _ _ (der_31769 v h) (by intro d hd; cases hd)))
def cl_35810 : CNF.NClause := [(78,true),(22,true),(13,false),(6,false),(4,false)]
theorem der_35810 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35810 :=
  CNF.rup_sound cl_35810 [cl_30569,cl_30399] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30569 v h) (hints_cons _ _ _ (der_30399 v h) (by intro d hd; cases hd)))
def cl_35815 : CNF.NClause := [(73,false),(116,false),(46,true),(93,false),(120,false),(107,false),(58,false),(40,true),(77,false),(91,false),(18,false),(86,false),(44,false),(42,true),(78,false),(68,false),(83,false),(63,false),(65,false),(69,false),(87,false),(4,false)]
theorem der_35815 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35815 :=
  CNF.rup_sound cl_35815 [cl_4481,cl_6273,cl_31887,cl_7964,cl_31210,cl_31480,cl_25679] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_4481 v h) (hints_cons _ _ _ (inp_6273 v h) (hints_cons _ _ _ (der_31887 v h) (hints_cons _ _ _ (inp_7964 v h) (hints_cons _ _ _ (der_31210 v h) (hints_cons _ _ _ (der_31480 v h) (hints_cons _ _ _ (der_25679 v h) (by intro d hd; cases hd))))))))
def cl_35816 : CNF.NClause := [(73,true),(18,false),(10,true),(7,true),(4,false)]
theorem der_35816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35816 :=
  CNF.rup_sound cl_35816 [cl_30547,cl_30548] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_30547 v h) (hints_cons _ _ _ (der_30548 v h) (by intro d hd; cases hd)))
def cl_35826 : CNF.NClause := [(77,true),(132,true),(151,true),(17,true),(16,false),(147,true),(139,true),(138,true),(131,true),(127,true)]
theorem der_35826 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35826 :=
  CNF.rup_sound cl_35826 [cl_29897,cl_35692,cl_15784,cl_15633] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_29897 v h) (hints_cons _ _ _ (der_35692 v h) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (der_15633 v h) (by intro d hd; cases hd)))))
def cl_35828 : CNF.NClause := [(91,true),(916,true),(926,true),(923,true),(921,true),(922,true),(914,true),(913,true),(12,true),(909,true),(906,true),(6,false),(902,true),(900,true)]
theorem der_35828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35828 :=
  CNF.rup_sound cl_35828 [cl_12706,cl_15878,cl_15669,cl_15703,cl_35201,cl_35435,cl_15884,cl_15891,cl_15682,cl_22899,cl_15715,cl_12700,cl_12757,cl_15691] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_12706 v h) (hints_cons _ _ _ (der_15878 v h) (hints_cons _ _ _ (der_15669 v h) (hints_cons _ _ _ (der_15703 v h) (hints_cons _ _ _ (der_35201 v h) (hints_cons _ _ _ (der_35435 v h) (hints_cons _ _ _ (der_15884 v h) (hints_cons _ _ _ (der_15891 v h) (hints_cons _ _ _ (der_15682 v h) (hints_cons _ _ _ (der_22899 v h) (hints_cons _ _ _ (der_15715 v h) (hints_cons _ _ _ (inp_12700 v h) (hints_cons _ _ _ (inp_12757 v h) (hints_cons _ _ _ (der_15691 v h) (by intro d hd; cases hd)))))))))))))))
def cl_35838 : CNF.NClause := [(93,true),(60,false),(58,false),(56,true)]
theorem der_35838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35838 :=
  CNF.rup_sound cl_35838 [cl_35537,cl_31783,cl_31561] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35537 v h) (hints_cons _ _ _ (der_31783 v h) (hints_cons _ _ _ (der_31561 v h) (by intro d hd; cases hd))))
def cl_35860 : CNF.NClause := [(104,true),(35,false),(59,false),(38,true),(41,true)]
theorem der_35860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35860 :=
  CNF.rup_sound cl_35860 [cl_35452,cl_31671] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35452 v h) (hints_cons _ _ _ (der_31671 v h) (by intro d hd; cases hd)))
def cl_35865 : CNF.NClause := [(67,true),(152,true),(135,true),(129,false),(150,true),(143,true),(20,true),(22,false),(23,true),(139,true),(136,true),(131,true),(127,true)]
theorem der_35865 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35865 :=
  CNF.rup_sound cl_35865 [cl_35082,cl_29796,cl_15787,cl_15790,cl_8110,cl_8076,cl_15619] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_35082 v h) (hints_cons _ _ _ (der_29796 v h) (hints_cons _ _ _ (der_15787 v h) (hints_cons _ _ _ (der_15790 v h) (hints_cons _ _ _ (inp_8110 v h) (hints_cons _ _ _ (inp_8076 v h) (hints_cons _ _ _ (der_15619 v h) (by intro d hd; cases hd))))))))
def cl_35868 : CNF.NClause := [(73,true),(137,true),(150,true),(147,true),(139,true),(138,true),(10,true),(7,true),(4,false),(127,true),(125,true)]
theorem der_35868 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35868 :=
  CNF.rup_sound cl_35868 [cl_15776,cl_30547,cl_35816,cl_35269,cl_15787,cl_15784,cl_15661,cl_15634,cl_8075] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_15776 v h) (hints_cons _ _ _ (der_30547 v h) (hints_cons _ _ _ (der_35816 v h) (hints_cons _ _ _ (der_35269 v h) (hints_cons _ _ _ (der_15787 v h) (hints_cons _ _ _ (der_15784 v h) (hints_cons _ _ _ (der_15661 v h) (hints_cons _ _ _ (der_15634 v h) (hints_cons _ _ _ (inp_8075 v h) (by intro d hd; cases hd))))))))))
def cl_35872 : CNF.NClause := [(46,false),(81,false),(80,true),(78,false),(79,false),(15,true)]
theorem der_35872 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_35872 :=
  CNF.rup_sound cl_35872 [cl_32944,cl_32945] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_32944 v h) (hints_cons _ _ _ (der_32945 v h) (by intro d hd; cases hd)))
def chunk023 : List CNF.NClause := [cl_34601,cl_34602,cl_34603,cl_34604,cl_34605,cl_34606,cl_34608,cl_34609,cl_34610,cl_34611,cl_34612,cl_34613,cl_34614,cl_34615,cl_34616,cl_34617,cl_34618,cl_34619,cl_34620,cl_34621,cl_34622,cl_34623,cl_34624,cl_34625,cl_34626,cl_34627,cl_34628,cl_34629,cl_34631,cl_34632,cl_34633,cl_34634,cl_34635,cl_34636,cl_34637,cl_34638,cl_34640,cl_34641,cl_34642,cl_34643,cl_34644,cl_34645,cl_34646,cl_34647,cl_34648,cl_34649,cl_34650,cl_34653,cl_34655,cl_34656,cl_34657,cl_34658,cl_34659,cl_34660,cl_34661,cl_34662,cl_34663,cl_34664,cl_34665,cl_34666,cl_34667,cl_34668,cl_34669,cl_34670,cl_34671,cl_34672,cl_34673,cl_34674,cl_34675,cl_34677,cl_34678,cl_34679,cl_34680,cl_34681,cl_34682,cl_34683,cl_34684,cl_34685,cl_34686,cl_34687,cl_34688,cl_34689,cl_34690,cl_34691,cl_34692,cl_34693,cl_34694,cl_34695,cl_34696,cl_34697,cl_34698,cl_34699,cl_34700,cl_34701,cl_34702,cl_34703,cl_34705,cl_34707,cl_34708,cl_34709,cl_34711,cl_34712,cl_34713,cl_34714,cl_34715,cl_34716,cl_34717,cl_34718,cl_34719,cl_34720,cl_34721,cl_34722,cl_34723,cl_34724,cl_34725,cl_34726,cl_34727,cl_34728,cl_34729,cl_34730,cl_34731,cl_34732,cl_34733,cl_34734,cl_34737,cl_34738,cl_34740,cl_34741,cl_34742,cl_34745,cl_34746,cl_34747,cl_34749,cl_34750,cl_34751,cl_34754,cl_34756,cl_34757,cl_34758,cl_34759,cl_34760,cl_34764,cl_34765,cl_34766,cl_34768,cl_34769,cl_34772,cl_34773,cl_34775,cl_34776,cl_34778,cl_34779,cl_34780,cl_34781,cl_34782,cl_34783,cl_34784,cl_34785,cl_34786,cl_34787,cl_34788,cl_34789,cl_34790,cl_34791,cl_34792,cl_34793,cl_34794,cl_34795,cl_34796,cl_34797,cl_34798,cl_34799,cl_34800,cl_34801,cl_34802,cl_34803,cl_34804,cl_34805,cl_34806,cl_34807,cl_34808,cl_34809,cl_34810,cl_34811,cl_34812,cl_34813,cl_34816,cl_34818,cl_34819,cl_34821,cl_34824,cl_34825,cl_34826,cl_34827,cl_34828,cl_34829,cl_34830,cl_34831,cl_34832,cl_34839,cl_34840,cl_34841,cl_34842,cl_34843,cl_34844,cl_34845,cl_34846,cl_34847,cl_34848,cl_34849,cl_34850,cl_34851,cl_34852,cl_34853,cl_34854,cl_34855,cl_34856,cl_34857,cl_34858,cl_34859,cl_34860,cl_34861,cl_34862,cl_34863,cl_34864,cl_34867,cl_34868,cl_34874,cl_34875,cl_34876,cl_34882,cl_34883,cl_34884,cl_34885,cl_34886,cl_34887,cl_34888,cl_34890,cl_34891,cl_34892,cl_34893,cl_34894,cl_34896,cl_34900,cl_34904,cl_34905,cl_34906,cl_34908,cl_34909,cl_34910,cl_34911,cl_34912,cl_34913,cl_34914,cl_34915,cl_34916,cl_34919,cl_34920,cl_34921,cl_34923,cl_34924,cl_34925,cl_34927,cl_34928,cl_34931,cl_34933,cl_34934,cl_34935,cl_34936,cl_34938,cl_34939,cl_34941,cl_34942,cl_34943,cl_34945,cl_34946,cl_34947,cl_34949,cl_34950,cl_34951,cl_34953,cl_34954,cl_34955,cl_34956,cl_34958,cl_34960,cl_34961,cl_34962,cl_34963,cl_34966,cl_34967,cl_34968,cl_34969,cl_34974,cl_34992,cl_34998,cl_35000,cl_35013,cl_35014,cl_35028,cl_35029,cl_35030,cl_35035,cl_35043,cl_35044,cl_35045,cl_35046,cl_35048,cl_35053,cl_35055,cl_35058,cl_35060,cl_35062,cl_35065,cl_35066,cl_35068,cl_35069,cl_35070,cl_35071,cl_35072,cl_35074,cl_35082,cl_35088,cl_35090,cl_35094,cl_35099,cl_35103,cl_35106,cl_35111,cl_35116,cl_35117,cl_35118,cl_35119,cl_35125,cl_35134,cl_35139,cl_35140,cl_35143,cl_35149,cl_35154,cl_35157,cl_35158,cl_35170,cl_35173,cl_35176,cl_35178,cl_35184,cl_35187,cl_35189,cl_35192,cl_35194,cl_35196,cl_35199,cl_35201,cl_35206,cl_35208,cl_35213,cl_35216,cl_35218,cl_35219,cl_35222,cl_35226,cl_35237,cl_35238,cl_35242,cl_35244,cl_35246,cl_35252,cl_35255,cl_35269,cl_35271,cl_35283,cl_35284,cl_35287,cl_35295,cl_35297,cl_35307,cl_35314,cl_35316,cl_35317,cl_35325,cl_35327,cl_35328,cl_35329,cl_35334,cl_35336,cl_35342,cl_35346,cl_35356,cl_35378,cl_35380,cl_35388,cl_35392,cl_35410,cl_35418,cl_35419,cl_35421,cl_35435,cl_35436,cl_35437,cl_35438,cl_35444,cl_35445,cl_35449,cl_35452,cl_35457,cl_35468,cl_35469,cl_35471,cl_35472,cl_35478,cl_35481,cl_35483,cl_35499,cl_35510,cl_35511,cl_35514,cl_35516,cl_35518,cl_35520,cl_35522,cl_35525,cl_35526,cl_35535,cl_35536,cl_35537,cl_35542,cl_35543,cl_35545,cl_35551,cl_35555,cl_35559,cl_35561,cl_35569,cl_35577,cl_35581,cl_35584,cl_35585,cl_35586,cl_35593,cl_35596,cl_35599,cl_35600,cl_35607,cl_35608,cl_35610,cl_35619,cl_35623,cl_35626,cl_35627,cl_35629,cl_35631,cl_35632,cl_35633,cl_35634,cl_35636,cl_35640,cl_35642,cl_35643,cl_35646,cl_35655,cl_35658,cl_35662,cl_35670,cl_35672,cl_35679,cl_35692,cl_35694,cl_35699,cl_35701,cl_35707,cl_35709,cl_35718,cl_35719,cl_35724,cl_35728,cl_35733,cl_35739,cl_35745,cl_35747,cl_35748,cl_35752,cl_35755,cl_35776,cl_35784,cl_35787,cl_35794,cl_35797,cl_35803,cl_35805,cl_35810,cl_35815,cl_35816,cl_35826,cl_35828,cl_35838,cl_35860,cl_35865,cl_35868,cl_35872]
theorem chunk_sound023 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ chunk023, CNF.Holds (v ∘ decodeVar) c :=
  (hints_cons _ _ _ (der_34601 v h) (hints_cons _ _ _ (der_34602 v h) (hints_cons _ _ _ (der_34603 v h) (hints_cons _ _ _ (der_34604 v h) (hints_cons _ _ _ (der_34605 v h) (hints_cons _ _ _ (der_34606 v h) (hints_cons _ _ _ (der_34608 v h) (hints_cons _ _ _ (der_34609 v h) (hints_cons _ _ _ (der_34610 v h) (hints_cons _ _ _ (der_34611 v h) (hints_cons _ _ _ (der_34612 v h) (hints_cons _ _ _ (der_34613 v h) (hints_cons _ _ _ (der_34614 v h) (hints_cons _ _ _ (der_34615 v h) (hints_cons _ _ _ (der_34616 v h) (hints_cons _ _ _ (der_34617 v h) (hints_cons _ _ _ (der_34618 v h) (hints_cons _ _ _ (der_34619 v h) (hints_cons _ _ _ (der_34620 v h) (hints_cons _ _ _ (der_34621 v h) (hints_cons _ _ _ (der_34622 v h) (hints_cons _ _ _ (der_34623 v h) (hints_cons _ _ _ (der_34624 v h) (hints_cons _ _ _ (der_34625 v h) (hints_cons _ _ _ (der_34626 v h) (hints_cons _ _ _ (der_34627 v h) (hints_cons _ _ _ (der_34628 v h) (hints_cons _ _ _ (der_34629 v h) (hints_cons _ _ _ (der_34631 v h) (hints_cons _ _ _ (der_34632 v h) (hints_cons _ _ _ (der_34633 v h) (hints_cons _ _ _ (der_34634 v h) (hints_cons _ _ _ (der_34635 v h) (hints_cons _ _ _ (der_34636 v h) (hints_cons _ _ _ (der_34637 v h) (hints_cons _ _ _ (der_34638 v h) (hints_cons _ _ _ (der_34640 v h) (hints_cons _ _ _ (der_34641 v h) (hints_cons _ _ _ (der_34642 v h) (hints_cons _ _ _ (der_34643 v h) (hints_cons _ _ _ (der_34644 v h) (hints_cons _ _ _ (der_34645 v h) (hints_cons _ _ _ (der_34646 v h) (hints_cons _ _ _ (der_34647 v h) (hints_cons _ _ _ (der_34648 v h) (hints_cons _ _ _ (der_34649 v h) (hints_cons _ _ _ (der_34650 v h) (hints_cons _ _ _ (der_34653 v h) (hints_cons _ _ _ (der_34655 v h) (hints_cons _ _ _ (der_34656 v h) (hints_cons _ _ _ (der_34657 v h) (hints_cons _ _ _ (der_34658 v h) (hints_cons _ _ _ (der_34659 v h) (hints_cons _ _ _ (der_34660 v h) (hints_cons _ _ _ (der_34661 v h) (hints_cons _ _ _ (der_34662 v h) (hints_cons _ _ _ (der_34663 v h) (hints_cons _ _ _ (der_34664 v h) (hints_cons _ _ _ (der_34665 v h) (hints_cons _ _ _ (der_34666 v h) (hints_cons _ _ _ (der_34667 v h) (hints_cons _ _ _ (der_34668 v h) (hints_cons _ _ _ (der_34669 v h) (hints_cons _ _ _ (der_34670 v h) (hints_cons _ _ _ (der_34671 v h) (hints_cons _ _ _ (der_34672 v h) (hints_cons _ _ _ (der_34673 v h) (hints_cons _ _ _ (der_34674 v h) (hints_cons _ _ _ (der_34675 v h) (hints_cons _ _ _ (der_34677 v h) (hints_cons _ _ _ (der_34678 v h) (hints_cons _ _ _ (der_34679 v h) (hints_cons _ _ _ (der_34680 v h) (hints_cons _ _ _ (der_34681 v h) (hints_cons _ _ _ (der_34682 v h) (hints_cons _ _ _ (der_34683 v h) (hints_cons _ _ _ (der_34684 v h) (hints_cons _ _ _ (der_34685 v h) (hints_cons _ _ _ (der_34686 v h) (hints_cons _ _ _ (der_34687 v h) (hints_cons _ _ _ (der_34688 v h) (hints_cons _ _ _ (der_34689 v h) (hints_cons _ _ _ (der_34690 v h) (hints_cons _ _ _ (der_34691 v h) (hints_cons _ _ _ (der_34692 v h) (hints_cons _ _ _ (der_34693 v h) (hints_cons _ _ _ (der_34694 v h) (hints_cons _ _ _ (der_34695 v h) (hints_cons _ _ _ (der_34696 v h) (hints_cons _ _ _ (der_34697 v h) (hints_cons _ _ _ (der_34698 v h) (hints_cons _ _ _ (der_34699 v h) (hints_cons _ _ _ (der_34700 v h) (hints_cons _ _ _ (der_34701 v h) (hints_cons _ _ _ (der_34702 v h) (hints_cons _ _ _ (der_34703 v h) (hints_cons _ _ _ (der_34705 v h) (hints_cons _ _ _ (der_34707 v h) (hints_cons _ _ _ (der_34708 v h) (hints_cons _ _ _ (der_34709 v h) (hints_cons _ _ _ (der_34711 v h) (hints_cons _ _ _ (der_34712 v h) (hints_cons _ _ _ (der_34713 v h) (hints_cons _ _ _ (der_34714 v h) (hints_cons _ _ _ (der_34715 v h) (hints_cons _ _ _ (der_34716 v h) (hints_cons _ _ _ (der_34717 v h) (hints_cons _ _ _ (der_34718 v h) (hints_cons _ _ _ (der_34719 v h) (hints_cons _ _ _ (der_34720 v h) (hints_cons _ _ _ (der_34721 v h) (hints_cons _ _ _ (der_34722 v h) (hints_cons _ _ _ (der_34723 v h) (hints_cons _ _ _ (der_34724 v h) (hints_cons _ _ _ (der_34725 v h) (hints_cons _ _ _ (der_34726 v h) (hints_cons _ _ _ (der_34727 v h) (hints_cons _ _ _ (der_34728 v h) (hints_cons _ _ _ (der_34729 v h) (hints_cons _ _ _ (der_34730 v h) (hints_cons _ _ _ (der_34731 v h) (hints_cons _ _ _ (der_34732 v h) (hints_cons _ _ _ (der_34733 v h) (hints_cons _ _ _ (der_34734 v h) (hints_cons _ _ _ (der_34737 v h) (hints_cons _ _ _ (der_34738 v h) (hints_cons _ _ _ (der_34740 v h) (hints_cons _ _ _ (der_34741 v h) (hints_cons _ _ _ (der_34742 v h) (hints_cons _ _ _ (der_34745 v h) (hints_cons _ _ _ (der_34746 v h) (hints_cons _ _ _ (der_34747 v h) (hints_cons _ _ _ (der_34749 v h) (hints_cons _ _ _ (der_34750 v h) (hints_cons _ _ _ (der_34751 v h) (hints_cons _ _ _ (der_34754 v h) (hints_cons _ _ _ (der_34756 v h) (hints_cons _ _ _ (der_34757 v h) (hints_cons _ _ _ (der_34758 v h) (hints_cons _ _ _ (der_34759 v h) (hints_cons _ _ _ (der_34760 v h) (hints_cons _ _ _ (der_34764 v h) (hints_cons _ _ _ (der_34765 v h) (hints_cons _ _ _ (der_34766 v h) (hints_cons _ _ _ (der_34768 v h) (hints_cons _ _ _ (der_34769 v h) (hints_cons _ _ _ (der_34772 v h) (hints_cons _ _ _ (der_34773 v h) (hints_cons _ _ _ (der_34775 v h) (hints_cons _ _ _ (der_34776 v h) (hints_cons _ _ _ (der_34778 v h) (hints_cons _ _ _ (der_34779 v h) (hints_cons _ _ _ (der_34780 v h) (hints_cons _ _ _ (der_34781 v h) (hints_cons _ _ _ (der_34782 v h) (hints_cons _ _ _ (der_34783 v h) (hints_cons _ _ _ (der_34784 v h) (hints_cons _ _ _ (der_34785 v h) (hints_cons _ _ _ (der_34786 v h) (hints_cons _ _ _ (der_34787 v h) (hints_cons _ _ _ (der_34788 v h) (hints_cons _ _ _ (der_34789 v h) (hints_cons _ _ _ (der_34790 v h) (hints_cons _ _ _ (der_34791 v h) (hints_cons _ _ _ (der_34792 v h) (hints_cons _ _ _ (der_34793 v h) (hints_cons _ _ _ (der_34794 v h) (hints_cons _ _ _ (der_34795 v h) (hints_cons _ _ _ (der_34796 v h) (hints_cons _ _ _ (der_34797 v h) (hints_cons _ _ _ (der_34798 v h) (hints_cons _ _ _ (der_34799 v h) (hints_cons _ _ _ (der_34800 v h) (hints_cons _ _ _ (der_34801 v h) (hints_cons _ _ _ (der_34802 v h) (hints_cons _ _ _ (der_34803 v h) (hints_cons _ _ _ (der_34804 v h) (hints_cons _ _ _ (der_34805 v h) (hints_cons _ _ _ (der_34806 v h) (hints_cons _ _ _ (der_34807 v h) (hints_cons _ _ _ (der_34808 v h) (hints_cons _ _ _ (der_34809 v h) (hints_cons _ _ _ (der_34810 v h) (hints_cons _ _ _ (der_34811 v h) (hints_cons _ _ _ (der_34812 v h) (hints_cons _ _ _ (der_34813 v h) (hints_cons _ _ _ (der_34816 v h) (hints_cons _ _ _ (der_34818 v h) (hints_cons _ _ _ (der_34819 v h) (hints_cons _ _ _ (der_34821 v h) (hints_cons _ _ _ (der_34824 v h) (hints_cons _ _ _ (der_34825 v h) (hints_cons _ _ _ (der_34826 v h) (hints_cons _ _ _ (der_34827 v h) (hints_cons _ _ _ (der_34828 v h) (hints_cons _ _ _ (der_34829 v h) (hints_cons _ _ _ (der_34830 v h) (hints_cons _ _ _ (der_34831 v h) (hints_cons _ _ _ (der_34832 v h) (hints_cons _ _ _ (der_34839 v h) (hints_cons _ _ _ (der_34840 v h) (hints_cons _ _ _ (der_34841 v h) (hints_cons _ _ _ (der_34842 v h) (hints_cons _ _ _ (der_34843 v h) (hints_cons _ _ _ (der_34844 v h) (hints_cons _ _ _ (der_34845 v h) (hints_cons _ _ _ (der_34846 v h) (hints_cons _ _ _ (der_34847 v h) (hints_cons _ _ _ (der_34848 v h) (hints_cons _ _ _ (der_34849 v h) (hints_cons _ _ _ (der_34850 v h) (hints_cons _ _ _ (der_34851 v h) (hints_cons _ _ _ (der_34852 v h) (hints_cons _ _ _ (der_34853 v h) (hints_cons _ _ _ (der_34854 v h) (hints_cons _ _ _ (der_34855 v h) (hints_cons _ _ _ (der_34856 v h) (hints_cons _ _ _ (der_34857 v h) (hints_cons _ _ _ (der_34858 v h) (hints_cons _ _ _ (der_34859 v h) (hints_cons _ _ _ (der_34860 v h) (hints_cons _ _ _ (der_34861 v h) (hints_cons _ _ _ (der_34862 v h) (hints_cons _ _ _ (der_34863 v h) (hints_cons _ _ _ (der_34864 v h) (hints_cons _ _ _ (der_34867 v h) (hints_cons _ _ _ (der_34868 v h) (hints_cons _ _ _ (der_34874 v h) (hints_cons _ _ _ (der_34875 v h) (hints_cons _ _ _ (der_34876 v h) (hints_cons _ _ _ (der_34882 v h) (hints_cons _ _ _ (der_34883 v h) (hints_cons _ _ _ (der_34884 v h) (hints_cons _ _ _ (der_34885 v h) (hints_cons _ _ _ (der_34886 v h) (hints_cons _ _ _ (der_34887 v h) (hints_cons _ _ _ (der_34888 v h) (hints_cons _ _ _ (der_34890 v h) (hints_cons _ _ _ (der_34891 v h) (hints_cons _ _ _ (der_34892 v h) (hints_cons _ _ _ (der_34893 v h) (hints_cons _ _ _ (der_34894 v h) (hints_cons _ _ _ (der_34896 v h) (hints_cons _ _ _ (der_34900 v h) (hints_cons _ _ _ (der_34904 v h) (hints_cons _ _ _ (der_34905 v h) (hints_cons _ _ _ (der_34906 v h) (hints_cons _ _ _ (der_34908 v h) (hints_cons _ _ _ (der_34909 v h) (hints_cons _ _ _ (der_34910 v h) (hints_cons _ _ _ (der_34911 v h) (hints_cons _ _ _ (der_34912 v h) (hints_cons _ _ _ (der_34913 v h) (hints_cons _ _ _ (der_34914 v h) (hints_cons _ _ _ (der_34915 v h) (hints_cons _ _ _ (der_34916 v h) (hints_cons _ _ _ (der_34919 v h) (hints_cons _ _ _ (der_34920 v h) (hints_cons _ _ _ (der_34921 v h) (hints_cons _ _ _ (der_34923 v h) (hints_cons _ _ _ (der_34924 v h) (hints_cons _ _ _ (der_34925 v h) (hints_cons _ _ _ (der_34927 v h) (hints_cons _ _ _ (der_34928 v h) (hints_cons _ _ _ (der_34931 v h) (hints_cons _ _ _ (der_34933 v h) (hints_cons _ _ _ (der_34934 v h) (hints_cons _ _ _ (der_34935 v h) (hints_cons _ _ _ (der_34936 v h) (hints_cons _ _ _ (der_34938 v h) (hints_cons _ _ _ (der_34939 v h) (hints_cons _ _ _ (der_34941 v h) (hints_cons _ _ _ (der_34942 v h) (hints_cons _ _ _ (der_34943 v h) (hints_cons _ _ _ (der_34945 v h) (hints_cons _ _ _ (der_34946 v h) (hints_cons _ _ _ (der_34947 v h) (hints_cons _ _ _ (der_34949 v h) (hints_cons _ _ _ (der_34950 v h) (hints_cons _ _ _ (der_34951 v h) (hints_cons _ _ _ (der_34953 v h) (hints_cons _ _ _ (der_34954 v h) (hints_cons _ _ _ (der_34955 v h) (hints_cons _ _ _ (der_34956 v h) (hints_cons _ _ _ (der_34958 v h) (hints_cons _ _ _ (der_34960 v h) (hints_cons _ _ _ (der_34961 v h) (hints_cons _ _ _ (der_34962 v h) (hints_cons _ _ _ (der_34963 v h) (hints_cons _ _ _ (der_34966 v h) (hints_cons _ _ _ (der_34967 v h) (hints_cons _ _ _ (der_34968 v h) (hints_cons _ _ _ (der_34969 v h) (hints_cons _ _ _ (der_34974 v h) (hints_cons _ _ _ (der_34992 v h) (hints_cons _ _ _ (der_34998 v h) (hints_cons _ _ _ (der_35000 v h) (hints_cons _ _ _ (der_35013 v h) (hints_cons _ _ _ (der_35014 v h) (hints_cons _ _ _ (der_35028 v h) (hints_cons _ _ _ (der_35029 v h) (hints_cons _ _ _ (der_35030 v h) (hints_cons _ _ _ (der_35035 v h) (hints_cons _ _ _ (der_35043 v h) (hints_cons _ _ _ (der_35044 v h) (hints_cons _ _ _ (der_35045 v h) (hints_cons _ _ _ (der_35046 v h) (hints_cons _ _ _ (der_35048 v h) (hints_cons _ _ _ (der_35053 v h) (hints_cons _ _ _ (der_35055 v h) (hints_cons _ _ _ (der_35058 v h) (hints_cons _ _ _ (der_35060 v h) (hints_cons _ _ _ (der_35062 v h) (hints_cons _ _ _ (der_35065 v h) (hints_cons _ _ _ (der_35066 v h) (hints_cons _ _ _ (der_35068 v h) (hints_cons _ _ _ (der_35069 v h) (hints_cons _ _ _ (der_35070 v h) (hints_cons _ _ _ (der_35071 v h) (hints_cons _ _ _ (der_35072 v h) (hints_cons _ _ _ (der_35074 v h) (hints_cons _ _ _ (der_35082 v h) (hints_cons _ _ _ (der_35088 v h) (hints_cons _ _ _ (der_35090 v h) (hints_cons _ _ _ (der_35094 v h) (hints_cons _ _ _ (der_35099 v h) (hints_cons _ _ _ (der_35103 v h) (hints_cons _ _ _ (der_35106 v h) (hints_cons _ _ _ (der_35111 v h) (hints_cons _ _ _ (der_35116 v h) (hints_cons _ _ _ (der_35117 v h) (hints_cons _ _ _ (der_35118 v h) (hints_cons _ _ _ (der_35119 v h) (hints_cons _ _ _ (der_35125 v h) (hints_cons _ _ _ (der_35134 v h) (hints_cons _ _ _ (der_35139 v h) (hints_cons _ _ _ (der_35140 v h) (hints_cons _ _ _ (der_35143 v h) (hints_cons _ _ _ (der_35149 v h) (hints_cons _ _ _ (der_35154 v h) (hints_cons _ _ _ (der_35157 v h) (hints_cons _ _ _ (der_35158 v h) (hints_cons _ _ _ (der_35170 v h) (hints_cons _ _ _ (der_35173 v h) (hints_cons _ _ _ (der_35176 v h) (hints_cons _ _ _ (der_35178 v h) (hints_cons _ _ _ (der_35184 v h) (hints_cons _ _ _ (der_35187 v h) (hints_cons _ _ _ (der_35189 v h) (hints_cons _ _ _ (der_35192 v h) (hints_cons _ _ _ (der_35194 v h) (hints_cons _ _ _ (der_35196 v h) (hints_cons _ _ _ (der_35199 v h) (hints_cons _ _ _ (der_35201 v h) (hints_cons _ _ _ (der_35206 v h) (hints_cons _ _ _ (der_35208 v h) (hints_cons _ _ _ (der_35213 v h) (hints_cons _ _ _ (der_35216 v h) (hints_cons _ _ _ (der_35218 v h) (hints_cons _ _ _ (der_35219 v h) (hints_cons _ _ _ (der_35222 v h) (hints_cons _ _ _ (der_35226 v h) (hints_cons _ _ _ (der_35237 v h) (hints_cons _ _ _ (der_35238 v h) (hints_cons _ _ _ (der_35242 v h) (hints_cons _ _ _ (der_35244 v h) (hints_cons _ _ _ (der_35246 v h) (hints_cons _ _ _ (der_35252 v h) (hints_cons _ _ _ (der_35255 v h) (hints_cons _ _ _ (der_35269 v h) (hints_cons _ _ _ (der_35271 v h) (hints_cons _ _ _ (der_35283 v h) (hints_cons _ _ _ (der_35284 v h) (hints_cons _ _ _ (der_35287 v h) (hints_cons _ _ _ (der_35295 v h) (hints_cons _ _ _ (der_35297 v h) (hints_cons _ _ _ (der_35307 v h) (hints_cons _ _ _ (der_35314 v h) (hints_cons _ _ _ (der_35316 v h) (hints_cons _ _ _ (der_35317 v h) (hints_cons _ _ _ (der_35325 v h) (hints_cons _ _ _ (der_35327 v h) (hints_cons _ _ _ (der_35328 v h) (hints_cons _ _ _ (der_35329 v h) (hints_cons _ _ _ (der_35334 v h) (hints_cons _ _ _ (der_35336 v h) (hints_cons _ _ _ (der_35342 v h) (hints_cons _ _ _ (der_35346 v h) (hints_cons _ _ _ (der_35356 v h) (hints_cons _ _ _ (der_35378 v h) (hints_cons _ _ _ (der_35380 v h) (hints_cons _ _ _ (der_35388 v h) (hints_cons _ _ _ (der_35392 v h) (hints_cons _ _ _ (der_35410 v h) (hints_cons _ _ _ (der_35418 v h) (hints_cons _ _ _ (der_35419 v h) (hints_cons _ _ _ (der_35421 v h) (hints_cons _ _ _ (der_35435 v h) (hints_cons _ _ _ (der_35436 v h) (hints_cons _ _ _ (der_35437 v h) (hints_cons _ _ _ (der_35438 v h) (hints_cons _ _ _ (der_35444 v h) (hints_cons _ _ _ (der_35445 v h) (hints_cons _ _ _ (der_35449 v h) (hints_cons _ _ _ (der_35452 v h) (hints_cons _ _ _ (der_35457 v h) (hints_cons _ _ _ (der_35468 v h) (hints_cons _ _ _ (der_35469 v h) (hints_cons _ _ _ (der_35471 v h) (hints_cons _ _ _ (der_35472 v h) (hints_cons _ _ _ (der_35478 v h) (hints_cons _ _ _ (der_35481 v h) (hints_cons _ _ _ (der_35483 v h) (hints_cons _ _ _ (der_35499 v h) (hints_cons _ _ _ (der_35510 v h) (hints_cons _ _ _ (der_35511 v h) (hints_cons _ _ _ (der_35514 v h) (hints_cons _ _ _ (der_35516 v h) (hints_cons _ _ _ (der_35518 v h) (hints_cons _ _ _ (der_35520 v h) (hints_cons _ _ _ (der_35522 v h) (hints_cons _ _ _ (der_35525 v h) (hints_cons _ _ _ (der_35526 v h) (hints_cons _ _ _ (der_35535 v h) (hints_cons _ _ _ (der_35536 v h) (hints_cons _ _ _ (der_35537 v h) (hints_cons _ _ _ (der_35542 v h) (hints_cons _ _ _ (der_35543 v h) (hints_cons _ _ _ (der_35545 v h) (hints_cons _ _ _ (der_35551 v h) (hints_cons _ _ _ (der_35555 v h) (hints_cons _ _ _ (der_35559 v h) (hints_cons _ _ _ (der_35561 v h) (hints_cons _ _ _ (der_35569 v h) (hints_cons _ _ _ (der_35577 v h) (hints_cons _ _ _ (der_35581 v h) (hints_cons _ _ _ (der_35584 v h) (hints_cons _ _ _ (der_35585 v h) (hints_cons _ _ _ (der_35586 v h) (hints_cons _ _ _ (der_35593 v h) (hints_cons _ _ _ (der_35596 v h) (hints_cons _ _ _ (der_35599 v h) (hints_cons _ _ _ (der_35600 v h) (hints_cons _ _ _ (der_35607 v h) (hints_cons _ _ _ (der_35608 v h) (hints_cons _ _ _ (der_35610 v h) (hints_cons _ _ _ (der_35619 v h) (hints_cons _ _ _ (der_35623 v h) (hints_cons _ _ _ (der_35626 v h) (hints_cons _ _ _ (der_35627 v h) (hints_cons _ _ _ (der_35629 v h) (hints_cons _ _ _ (der_35631 v h) (hints_cons _ _ _ (der_35632 v h) (hints_cons _ _ _ (der_35633 v h) (hints_cons _ _ _ (der_35634 v h) (hints_cons _ _ _ (der_35636 v h) (hints_cons _ _ _ (der_35640 v h) (hints_cons _ _ _ (der_35642 v h) (hints_cons _ _ _ (der_35643 v h) (hints_cons _ _ _ (der_35646 v h) (hints_cons _ _ _ (der_35655 v h) (hints_cons _ _ _ (der_35658 v h) (hints_cons _ _ _ (der_35662 v h) (hints_cons _ _ _ (der_35670 v h) (hints_cons _ _ _ (der_35672 v h) (hints_cons _ _ _ (der_35679 v h) (hints_cons _ _ _ (der_35692 v h) (hints_cons _ _ _ (der_35694 v h) (hints_cons _ _ _ (der_35699 v h) (hints_cons _ _ _ (der_35701 v h) (hints_cons _ _ _ (der_35707 v h) (hints_cons _ _ _ (der_35709 v h) (hints_cons _ _ _ (der_35718 v h) (hints_cons _ _ _ (der_35719 v h) (hints_cons _ _ _ (der_35724 v h) (hints_cons _ _ _ (der_35728 v h) (hints_cons _ _ _ (der_35733 v h) (hints_cons _ _ _ (der_35739 v h) (hints_cons _ _ _ (der_35745 v h) (hints_cons _ _ _ (der_35747 v h) (hints_cons _ _ _ (der_35748 v h) (hints_cons _ _ _ (der_35752 v h) (hints_cons _ _ _ (der_35755 v h) (hints_cons _ _ _ (der_35776 v h) (hints_cons _ _ _ (der_35784 v h) (hints_cons _ _ _ (der_35787 v h) (hints_cons _ _ _ (der_35794 v h) (hints_cons _ _ _ (der_35797 v h) (hints_cons _ _ _ (der_35803 v h) (hints_cons _ _ _ (der_35805 v h) (hints_cons _ _ _ (der_35810 v h) (hints_cons _ _ _ (der_35815 v h) (hints_cons _ _ _ (der_35816 v h) (hints_cons _ _ _ (der_35826 v h) (hints_cons _ _ _ (der_35828 v h) (hints_cons _ _ _ (der_35838 v h) (hints_cons _ _ _ (der_35860 v h) (hints_cons _ _ _ (der_35865 v h) (hints_cons _ _ _ (der_35868 v h) (hints_cons _ _ _ (der_35872 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def prefix023 := prefix022 ++ chunk023
theorem prefix_sound023 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix023, CNF.Holds (v ∘ decodeVar) c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact prefix_sound022 v h c hc
  · exact chunk_sound023 v h c hc
end Percolation.NReplay
