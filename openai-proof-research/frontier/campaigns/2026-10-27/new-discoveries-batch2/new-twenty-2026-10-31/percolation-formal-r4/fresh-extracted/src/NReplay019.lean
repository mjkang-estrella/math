import NReplay018
namespace Percolation.NReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cl_32303 : CNF.NClause := [(36,false),(86,true),(5,false),(92,false),(85,false),(83,true)]
theorem der_32303 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32303 :=
  CNF.rup_sound cl_32303 [cl_26646,cl_32298] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26646 v h) (hints_cons _ _ _ (der_32298 v h) (by intro d hd; cases hd)))
def cl_32304 : CNF.NClause := [(36,false),(84,true),(5,true),(92,false),(85,false),(83,true)]
theorem der_32304 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32304 :=
  CNF.rup_sound cl_32304 [cl_26647,cl_32288] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26647 v h) (hints_cons _ _ _ (der_32288 v h) (by intro d hd; cases hd)))
def cl_32305 : CNF.NClause := [(36,false),(82,false),(5,true),(92,false),(84,false),(83,false)]
theorem der_32305 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32305 :=
  CNF.rup_sound cl_32305 [cl_26649,cl_32300] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26649 v h) (hints_cons _ _ _ (der_32300 v h) (by intro d hd; cases hd)))
def cl_32306 : CNF.NClause := [(36,false),(82,true),(92,false),(84,false),(83,false),(5,true)]
theorem der_32306 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32306 :=
  CNF.rup_sound cl_32306 [cl_26651,cl_26620] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26651 v h) (hints_cons _ _ _ (der_26620 v h) (by intro d hd; cases hd)))
def cl_32307 : CNF.NClause := [(36,false),(92,false),(5,false),(82,false),(84,false),(85,true)]
theorem der_32307 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32307 :=
  CNF.rup_sound cl_32307 [cl_26652,cl_32290] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26652 v h) (hints_cons _ _ _ (der_32290 v h) (by intro d hd; cases hd)))
def cl_32308 : CNF.NClause := [(36,false),(82,false),(5,true),(92,false),(84,false),(83,true)]
theorem der_32308 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32308 :=
  CNF.rup_sound cl_32308 [cl_26653,cl_32289] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26653 v h) (hints_cons _ _ _ (der_32289 v h) (by intro d hd; cases hd)))
def cl_32309 : CNF.NClause := [(36,false),(84,false),(5,false),(92,false),(85,true),(83,true)]
theorem der_32309 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32309 :=
  CNF.rup_sound cl_32309 [cl_26654,cl_32307] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26654 v h) (hints_cons _ _ _ (der_32307 v h) (by intro d hd; cases hd)))
def cl_32310 : CNF.NClause := [(36,false),(84,false),(5,true),(92,false),(85,true),(83,true)]
theorem der_32310 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32310 :=
  CNF.rup_sound cl_32310 [cl_26655,cl_32291] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26655 v h) (hints_cons _ _ _ (der_32291 v h) (by intro d hd; cases hd)))
def cl_32311 : CNF.NClause := [(36,false),(83,false),(5,false),(92,false),(82,false),(86,true)]
theorem der_32311 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32311 :=
  CNF.rup_sound cl_32311 [cl_26656,cl_26648] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26656 v h) (hints_cons _ _ _ (der_26648 v h) (by intro d hd; cases hd)))
def cl_32312 : CNF.NClause := [(36,false),(84,true),(5,false),(92,false),(83,false),(82,true)]
theorem der_32312 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32312 :=
  CNF.rup_sound cl_32312 [cl_26658,cl_26642] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26658 v h) (hints_cons _ _ _ (der_26642 v h) (by intro d hd; cases hd)))
def cl_32313 : CNF.NClause := [(36,false),(86,true),(82,true),(84,true),(92,false),(83,false)]
theorem der_32313 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32313 :=
  CNF.rup_sound cl_32313 [cl_26659,cl_32312] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26659 v h) (hints_cons _ _ _ (der_32312 v h) (by intro d hd; cases hd)))
def cl_32314 : CNF.NClause := [(36,false),(84,true),(5,false),(86,true),(92,false),(82,false)]
theorem der_32314 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32314 :=
  CNF.rup_sound cl_32314 [cl_26660,cl_32311] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26660 v h) (hints_cons _ _ _ (der_32311 v h) (by intro d hd; cases hd)))
def cl_32315 : CNF.NClause := [(36,false),(84,true),(86,true),(92,false),(82,false),(83,true)]
theorem der_32315 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32315 :=
  CNF.rup_sound cl_32315 [cl_26661,cl_32314] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26661 v h) (hints_cons _ _ _ (der_32314 v h) (by intro d hd; cases hd)))
def cl_32316 : CNF.NClause := [(36,false),(5,false),(92,false),(85,true),(82,true),(83,true)]
theorem der_32316 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32316 :=
  CNF.rup_sound cl_32316 [cl_26662,cl_32309] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26662 v h) (hints_cons _ _ _ (der_32309 v h) (by intro d hd; cases hd)))
def cl_32317 : CNF.NClause := [(36,false),(85,true),(5,true),(92,false),(82,true),(83,true)]
theorem der_32317 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32317 :=
  CNF.rup_sound cl_32317 [cl_26663,cl_32310] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26663 v h) (hints_cons _ _ _ (der_32310 v h) (by intro d hd; cases hd)))
def cl_32318 : CNF.NClause := [(36,false),(84,false),(85,false),(86,false),(5,true),(83,false)]
theorem der_32318 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32318 :=
  CNF.rup_sound cl_32318 [cl_26666,cl_26664] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26666 v h) (hints_cons _ _ _ (der_26664 v h) (by intro d hd; cases hd)))
def cl_32319 : CNF.NClause := [(36,false),(86,false),(85,false),(5,true),(82,false),(84,false)]
theorem der_32319 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32319 :=
  CNF.rup_sound cl_32319 [cl_26668,cl_26664] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26668 v h) (hints_cons _ _ _ (der_26664 v h) (by intro d hd; cases hd)))
def cl_32320 : CNF.NClause := [(36,false),(86,false),(85,false),(5,true),(84,false),(83,true)]
theorem der_32320 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32320 :=
  CNF.rup_sound cl_32320 [cl_26670,cl_32319] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26670 v h) (hints_cons _ _ _ (der_32319 v h) (by intro d hd; cases hd)))
def cl_32321 : CNF.NClause := [(36,false),(86,false),(85,false),(82,false),(5,true),(83,false)]
theorem der_32321 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32321 :=
  CNF.rup_sound cl_32321 [cl_26672,cl_26611] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26672 v h) (hints_cons _ _ _ (der_26611 v h) (by intro d hd; cases hd)))
def cl_32322 : CNF.NClause := [(36,false),(85,false),(84,true),(5,true),(82,false),(86,false)]
theorem der_32322 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32322 :=
  CNF.rup_sound cl_32322 [cl_26676,cl_32321] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26676 v h) (hints_cons _ _ _ (der_32321 v h) (by intro d hd; cases hd)))
def cl_32323 : CNF.NClause := [(36,false),(84,true),(5,false),(85,false),(86,false),(82,true)]
theorem der_32323 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32323 :=
  CNF.rup_sound cl_32323 [cl_26677,cl_32287] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26677 v h) (hints_cons _ _ _ (der_32287 v h) (by intro d hd; cases hd)))
def cl_32324 : CNF.NClause := [(36,false),(86,false),(85,false),(5,true),(82,true),(83,true)]
theorem der_32324 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32324 :=
  CNF.rup_sound cl_32324 [cl_26678,cl_32288] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26678 v h) (hints_cons _ _ _ (der_32288 v h) (by intro d hd; cases hd)))
def cl_32325 : CNF.NClause := [(36,false),(86,false),(5,true),(82,false),(84,false),(83,false)]
theorem der_32325 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32325 :=
  CNF.rup_sound cl_32325 [cl_26680,cl_26664] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26680 v h) (hints_cons _ _ _ (der_26664 v h) (by intro d hd; cases hd)))
def cl_32326 : CNF.NClause := [(36,false),(86,false),(84,false),(83,false),(5,true),(82,true)]
theorem der_32326 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32326 :=
  CNF.rup_sound cl_32326 [cl_26682,cl_32318] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26682 v h) (hints_cons _ _ _ (der_32318 v h) (by intro d hd; cases hd)))
def cl_32327 : CNF.NClause := [(36,false),(86,false),(5,false),(84,false),(85,true),(82,true)]
theorem der_32327 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32327 :=
  CNF.rup_sound cl_32327 [cl_26685,cl_26681] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26685 v h) (hints_cons _ _ _ (der_26681 v h) (by intro d hd; cases hd)))
def cl_32328 : CNF.NClause := [(36,false),(86,false),(84,false),(85,true),(83,true),(92,true)]
theorem der_32328 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32328 :=
  CNF.rup_sound cl_32328 [cl_26686,cl_26684] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26686 v h) (hints_cons _ _ _ (der_26684 v h) (by intro d hd; cases hd)))
def cl_32329 : CNF.NClause := [(36,false),(86,false),(84,true),(83,false),(85,true),(92,true)]
theorem der_32329 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32329 :=
  CNF.rup_sound cl_32329 [cl_26690,cl_26689] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26690 v h) (hints_cons _ _ _ (der_26689 v h) (by intro d hd; cases hd)))
def cl_32330 : CNF.NClause := [(36,false),(86,false),(84,true),(5,false),(82,false),(85,true)]
theorem der_32330 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32330 :=
  CNF.rup_sound cl_32330 [cl_26691,cl_32293] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26691 v h) (hints_cons _ _ _ (der_32293 v h) (by intro d hd; cases hd)))
def cl_32331 : CNF.NClause := [(36,false),(86,false),(84,true),(82,false),(85,true),(83,true)]
theorem der_32331 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32331 :=
  CNF.rup_sound cl_32331 [cl_26692,cl_32330] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26692 v h) (hints_cons _ _ _ (der_32330 v h) (by intro d hd; cases hd)))
def cl_32332 : CNF.NClause := [(36,false),(84,true),(5,false),(86,false),(82,true),(83,true)]
theorem der_32332 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32332 :=
  CNF.rup_sound cl_32332 [cl_26693,cl_32323] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26693 v h) (hints_cons _ _ _ (der_32323 v h) (by intro d hd; cases hd)))
def cl_32333 : CNF.NClause := [(36,false),(84,true),(86,false),(85,true),(82,true),(83,true)]
theorem der_32333 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32333 :=
  CNF.rup_sound cl_32333 [cl_26694,cl_32296] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26694 v h) (hints_cons _ _ _ (der_32296 v h) (by intro d hd; cases hd)))
def cl_32334 : CNF.NClause := [(36,false),(85,false),(5,true),(82,false),(84,false),(83,false)]
theorem der_32334 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32334 :=
  CNF.rup_sound cl_32334 [cl_26696,cl_32318] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26696 v h) (hints_cons _ _ _ (der_32318 v h) (by intro d hd; cases hd)))
def cl_32335 : CNF.NClause := [(36,false),(84,false),(85,false),(5,true),(83,false),(82,true)]
theorem der_32335 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32335 :=
  CNF.rup_sound cl_32335 [cl_26698,cl_26635] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26698 v h) (hints_cons _ _ _ (der_26635 v h) (by intro d hd; cases hd)))
def cl_32336 : CNF.NClause := [(36,false),(85,false),(5,true),(82,false),(84,false),(83,true)]
theorem der_32336 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32336 :=
  CNF.rup_sound cl_32336 [cl_26700,cl_32319] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26700 v h) (hints_cons _ _ _ (der_32319 v h) (by intro d hd; cases hd)))
def cl_32338 : CNF.NClause := [(36,false),(85,false),(5,true),(84,false),(83,true),(92,true)]
theorem der_32338 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32338 :=
  CNF.rup_sound cl_32338 [cl_26702,cl_32320] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26702 v h) (hints_cons _ _ _ (der_32320 v h) (by intro d hd; cases hd)))
def cl_32339 : CNF.NClause := [(36,false),(84,true),(5,true),(85,false),(82,false),(83,false)]
theorem der_32339 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32339 :=
  CNF.rup_sound cl_32339 [cl_26704,cl_32321] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26704 v h) (hints_cons _ _ _ (der_32321 v h) (by intro d hd; cases hd)))
def cl_32340 : CNF.NClause := [(36,false),(84,true),(5,false),(85,false),(83,false),(82,true)]
theorem der_32340 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32340 :=
  CNF.rup_sound cl_32340 [cl_26705,cl_32312] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26705 v h) (hints_cons _ _ _ (der_32312 v h) (by intro d hd; cases hd)))
def cl_32341 : CNF.NClause := [(36,false),(86,true),(84,true),(85,false),(83,false),(5,true)]
theorem der_32341 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32341 :=
  CNF.rup_sound cl_32341 [cl_26706,cl_32339] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26706 v h) (hints_cons _ _ _ (der_32339 v h) (by intro d hd; cases hd)))
def cl_32342 : CNF.NClause := [(36,false),(5,false),(86,true),(85,false),(82,false),(83,true)]
theorem der_32342 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32342 :=
  CNF.rup_sound cl_32342 [cl_26707,cl_26699] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26707 v h) (hints_cons _ _ _ (der_26699 v h) (by intro d hd; cases hd)))
def cl_32343 : CNF.NClause := [(36,false),(84,true),(86,true),(5,true),(85,false),(82,false)]
theorem der_32343 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32343 :=
  CNF.rup_sound cl_32343 [cl_26708,cl_32341] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26708 v h) (hints_cons _ _ _ (der_32341 v h) (by intro d hd; cases hd)))
def cl_32344 : CNF.NClause := [(36,false),(85,false),(86,true),(5,false),(83,true),(92,true)]
theorem der_32344 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32344 :=
  CNF.rup_sound cl_32344 [cl_26709,cl_32342] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26709 v h) (hints_cons _ _ _ (der_32342 v h) (by intro d hd; cases hd)))
def cl_32345 : CNF.NClause := [(36,false),(84,true),(86,true),(5,true),(85,false),(92,true)]
theorem der_32345 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32345 :=
  CNF.rup_sound cl_32345 [cl_26710,cl_32341] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26710 v h) (hints_cons _ _ _ (der_32341 v h) (by intro d hd; cases hd)))
def cl_32346 : CNF.NClause := [(36,false),(83,false),(5,false),(82,false),(84,false),(86,true)]
theorem der_32346 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32346 :=
  CNF.rup_sound cl_32346 [cl_26711,cl_32311] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26711 v h) (hints_cons _ _ _ (der_32311 v h) (by intro d hd; cases hd)))
def cl_32347 : CNF.NClause := [(36,false),(84,false),(86,true),(5,false),(83,false),(92,true)]
theorem der_32347 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32347 :=
  CNF.rup_sound cl_32347 [cl_26713,cl_32346] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26713 v h) (hints_cons _ _ _ (der_32346 v h) (by intro d hd; cases hd)))
def cl_32348 : CNF.NClause := [(36,false),(84,false),(5,true),(83,false),(82,true),(92,true)]
theorem der_32348 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32348 :=
  CNF.rup_sound cl_32348 [cl_26714,cl_32326] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26714 v h) (hints_cons _ _ _ (der_32326 v h) (by intro d hd; cases hd)))
def cl_32349 : CNF.NClause := [(36,false),(84,false),(82,false),(5,false),(85,true),(83,true)]
theorem der_32349 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32349 :=
  CNF.rup_sound cl_32349 [cl_26715,cl_32309] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26715 v h) (hints_cons _ _ _ (der_32309 v h) (by intro d hd; cases hd)))
def cl_32350 : CNF.NClause := [(36,false),(84,false),(86,true),(5,true),(82,false),(83,true)]
theorem der_32350 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32350 :=
  CNF.rup_sound cl_32350 [cl_26716,cl_32336] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26716 v h) (hints_cons _ _ _ (der_32336 v h) (by intro d hd; cases hd)))
def cl_32351 : CNF.NClause := [(36,false),(84,false),(86,true),(5,false),(85,true),(83,true)]
theorem der_32351 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32351 :=
  CNF.rup_sound cl_32351 [cl_26717,cl_32309] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26717 v h) (hints_cons _ _ _ (der_32309 v h) (by intro d hd; cases hd)))
def cl_32352 : CNF.NClause := [(36,false),(84,false),(86,true),(85,true),(82,true),(83,true)]
theorem der_32352 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32352 :=
  CNF.rup_sound cl_32352 [cl_26718,cl_32351] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26718 v h) (hints_cons _ _ _ (der_32351 v h) (by intro d hd; cases hd)))
def cl_32353 : CNF.NClause := [(36,false),(85,true),(5,false),(84,true),(82,false),(83,false)]
theorem der_32353 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32353 :=
  CNF.rup_sound cl_32353 [cl_26719,cl_26687] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26719 v h) (hints_cons _ _ _ (der_26687 v h) (by intro d hd; cases hd)))
def cl_32354 : CNF.NClause := [(36,false),(84,true),(5,true),(82,false),(83,false),(92,true)]
theorem der_32354 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32354 :=
  CNF.rup_sound cl_32354 [cl_26720,cl_32339] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26720 v h) (hints_cons _ _ _ (der_32339 v h) (by intro d hd; cases hd)))
def cl_32356 : CNF.NClause := [(36,false),(92,true),(84,true),(83,false),(85,true),(82,true)]
theorem der_32356 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32356 :=
  CNF.rup_sound cl_32356 [cl_26722,cl_32329] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26722 v h) (hints_cons _ _ _ (der_32329 v h) (by intro d hd; cases hd)))
def cl_32358 : CNF.NClause := [(36,false),(84,true),(86,true),(5,true),(82,false),(92,true)]
theorem der_32358 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32358 :=
  CNF.rup_sound cl_32358 [cl_26724,cl_32354] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26724 v h) (hints_cons _ _ _ (der_32354 v h) (by intro d hd; cases hd)))
def cl_32360 : CNF.NClause := [(36,false),(84,true),(86,true),(5,true),(83,true),(92,true)]
theorem der_32360 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32360 :=
  CNF.rup_sound cl_32360 [cl_26726,cl_32358] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26726 v h) (hints_cons _ _ _ (der_32358 v h) (by intro d hd; cases hd)))
def cl_32361 : CNF.NClause := [(73,false),(7,true),(18,true),(4,true),(10,true),(21,true)]
theorem der_32361 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32361 :=
  CNF.rup_sound cl_32361 [cl_736,cl_23678] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_736 v h) (hints_cons _ _ _ (der_23678 v h) (by intro d hd; cases hd)))
def cl_32362 : CNF.NClause := [(73,false),(18,true),(4,true),(28,true),(10,true),(7,true)]
theorem der_32362 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32362 :=
  CNF.rup_sound cl_32362 [cl_752,cl_23678] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_752 v h) (hints_cons _ _ _ (der_23678 v h) (by intro d hd; cases hd)))
def cl_32363 : CNF.NClause := [(73,false),(10,true),(7,true),(4,true),(28,true),(21,true)]
theorem der_32363 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32363 :=
  CNF.rup_sound cl_32363 [cl_760,cl_23678] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_760 v h) (hints_cons _ _ _ (der_23678 v h) (by intro d hd; cases hd)))
def cl_32364 : CNF.NClause := [(49,false),(69,false),(86,false),(18,true),(73,false),(65,false)]
theorem der_32364 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32364 :=
  CNF.rup_sound cl_32364 [cl_26729,cl_26727] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26729 v h) (hints_cons _ _ _ (der_26727 v h) (by intro d hd; cases hd)))
def cl_32365 : CNF.NClause := [(71,false),(13,true),(19,true),(26,true),(1,true),(7,true)]
theorem der_32365 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32365 :=
  CNF.rup_sound cl_32365 [cl_624,cl_23679] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_624 v h) (hints_cons _ _ _ (der_23679 v h) (by intro d hd; cases hd)))
def cl_32366 : CNF.NClause := [(71,false),(13,true),(7,true),(26,true),(1,true),(20,true)]
theorem der_32366 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32366 :=
  CNF.rup_sound cl_32366 [cl_632,cl_23679] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_632 v h) (hints_cons _ _ _ (der_23679 v h) (by intro d hd; cases hd)))
def cl_32367 : CNF.NClause := [(71,false),(19,true),(26,true),(1,true),(20,true),(7,true)]
theorem der_32367 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32367 :=
  CNF.rup_sound cl_32367 [cl_636,cl_23679] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_636 v h) (hints_cons _ _ _ (der_23679 v h) (by intro d hd; cases hd)))
def cl_32368 : CNF.NClause := [(71,false),(13,true),(19,true),(26,true),(1,true),(20,true)]
theorem der_32368 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32368 :=
  CNF.rup_sound cl_32368 [cl_638,cl_23679] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_638 v h) (hints_cons _ _ _ (der_23679 v h) (by intro d hd; cases hd)))
def cl_32369 : CNF.NClause := [(71,false),(13,true),(26,true),(20,true),(7,true),(19,true)]
theorem der_32369 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32369 :=
  CNF.rup_sound cl_32369 [cl_639,cl_23679] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_639 v h) (hints_cons _ _ _ (der_23679 v h) (by intro d hd; cases hd)))
def cl_32370 : CNF.NClause := [(57,false),(71,false),(62,true),(91,false),(26,true),(83,false)]
theorem der_32370 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32370 :=
  CNF.rup_sound cl_32370 [cl_26732,cl_26731] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26732 v h) (hints_cons _ _ _ (der_26731 v h) (by intro d hd; cases hd)))
def cl_32371 : CNF.NClause := [(57,false),(71,false),(62,true),(91,false),(79,false),(26,true)]
theorem der_32371 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32371 :=
  CNF.rup_sound cl_32371 [cl_26734,cl_26733] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26734 v h) (hints_cons _ _ _ (der_26733 v h) (by intro d hd; cases hd)))
def cl_32372 : CNF.NClause := [(57,false),(71,false),(62,true),(91,false),(26,true),(75,false)]
theorem der_32372 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32372 :=
  CNF.rup_sound cl_32372 [cl_26735,cl_32371] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26735 v h) (hints_cons _ _ _ (der_32371 v h) (by intro d hd; cases hd)))
def cl_32373 : CNF.NClause := [(57,false),(71,false),(62,true),(75,true),(26,true),(91,false)]
theorem der_32373 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32373 :=
  CNF.rup_sound cl_32373 [cl_26736,cl_32371] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26736 v h) (hints_cons _ _ _ (der_32371 v h) (by intro d hd; cases hd)))
def cl_32374 : CNF.NClause := [(57,false),(26,true),(62,true),(79,false),(71,false),(83,false)]
theorem der_32374 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32374 :=
  CNF.rup_sound cl_32374 [cl_26738,cl_26737] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26738 v h) (hints_cons _ _ _ (der_26737 v h) (by intro d hd; cases hd)))
def cl_32375 : CNF.NClause := [(57,false),(83,false),(62,true),(71,false),(75,false),(26,true)]
theorem der_32375 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32375 :=
  CNF.rup_sound cl_32375 [cl_26739,cl_32372] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26739 v h) (hints_cons _ _ _ (der_32372 v h) (by intro d hd; cases hd)))
def cl_32376 : CNF.NClause := [(57,false),(71,false),(62,true),(75,true),(26,true),(83,false)]
theorem der_32376 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32376 :=
  CNF.rup_sound cl_32376 [cl_26740,cl_32374] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26740 v h) (hints_cons _ _ _ (der_32374 v h) (by intro d hd; cases hd)))
def cl_32377 : CNF.NClause := [(57,false),(62,true),(79,false),(71,false),(75,false),(26,true)]
theorem der_32377 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32377 :=
  CNF.rup_sound cl_32377 [cl_26741,cl_32372] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26741 v h) (hints_cons _ _ _ (der_32372 v h) (by intro d hd; cases hd)))
def cl_32378 : CNF.NClause := [(57,false),(62,true),(75,true),(79,false),(71,false),(26,true)]
theorem der_32378 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32378 :=
  CNF.rup_sound cl_32378 [cl_26742,cl_32374] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26742 v h) (hints_cons _ _ _ (der_32374 v h) (by intro d hd; cases hd)))
def cl_32379 : CNF.NClause := [(57,false),(75,false),(62,true),(79,true),(71,false),(26,true)]
theorem der_32379 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32379 :=
  CNF.rup_sound cl_32379 [cl_26743,cl_32375] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26743 v h) (hints_cons _ _ _ (der_32375 v h) (by intro d hd; cases hd)))
def cl_32380 : CNF.NClause := [(57,false),(71,false),(62,true),(75,true),(79,true),(26,true)]
theorem der_32380 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32380 :=
  CNF.rup_sound cl_32380 [cl_26744,cl_32373] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26744 v h) (hints_cons _ _ _ (der_32373 v h) (by intro d hd; cases hd)))
def cl_32381 : CNF.NClause := [(44,false),(78,true),(13,true),(72,false),(71,false),(65,false)]
theorem der_32381 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32381 :=
  CNF.rup_sound cl_32381 [cl_26748,cl_26745] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26748 v h) (hints_cons _ _ _ (der_26745 v h) (by intro d hd; cases hd)))
def cl_32382 : CNF.NClause := [(50,false),(71,false),(63,false),(85,false),(90,false),(19,true)]
theorem der_32382 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32382 :=
  CNF.rup_sound cl_32382 [cl_26750,cl_26749] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26750 v h) (hints_cons _ _ _ (der_26749 v h) (by intro d hd; cases hd)))
def cl_32384 : CNF.NClause := [(50,false),(77,false),(19,true),(63,false),(85,false),(71,false)]
theorem der_32384 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32384 :=
  CNF.rup_sound cl_32384 [cl_26754,cl_26753] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26754 v h) (hints_cons _ _ _ (der_26753 v h) (by intro d hd; cases hd)))
def cl_32385 : CNF.NClause := [(50,false),(63,false),(85,false),(71,false),(74,false),(19,true)]
theorem der_32385 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32385 :=
  CNF.rup_sound cl_32385 [cl_26755,cl_32382] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26755 v h) (hints_cons _ _ _ (der_32382 v h) (by intro d hd; cases hd)))
def cl_32386 : CNF.NClause := [(50,false),(85,false),(74,true),(63,false),(19,true),(71,false)]
theorem der_32386 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32386 :=
  CNF.rup_sound cl_32386 [cl_26756,cl_32384] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26756 v h) (hints_cons _ _ _ (der_32384 v h) (by intro d hd; cases hd)))
def cl_32387 : CNF.NClause := [(50,false),(74,true),(19,true),(77,false),(63,false),(71,false)]
theorem der_32387 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32387 :=
  CNF.rup_sound cl_32387 [cl_26757,cl_32384] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26757 v h) (hints_cons _ _ _ (der_32384 v h) (by intro d hd; cases hd)))
def cl_32388 : CNF.NClause := [(50,false),(85,true),(74,true),(63,false),(71,false),(19,true)]
theorem der_32388 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32388 :=
  CNF.rup_sound cl_32388 [cl_26758,cl_32387] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26758 v h) (hints_cons _ _ _ (der_32387 v h) (by intro d hd; cases hd)))
def cl_32389 : CNF.NClause := [(48,false),(77,true),(88,false),(17,true),(64,false),(70,false)]
theorem der_32389 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32389 :=
  CNF.rup_sound cl_32389 [cl_26760,cl_32086] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26760 v h) (hints_cons _ _ _ (der_32086 v h) (by intro d hd; cases hd)))
def cl_32390 : CNF.NClause := [(81,false),(28,true),(1,true),(9,true),(12,true),(15,true)]
theorem der_32390 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32390 :=
  CNF.rup_sound cl_32390 [cl_1264,cl_23681] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1264 v h) (hints_cons _ _ _ (der_23681 v h) (by intro d hd; cases hd)))
def cl_32391 : CNF.NClause := [(81,false),(28,true),(9,true),(23,true),(12,true),(1,true)]
theorem der_32391 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32391 :=
  CNF.rup_sound cl_32391 [cl_1272,cl_23681] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1272 v h) (hints_cons _ _ _ (der_23681 v h) (by intro d hd; cases hd)))
def cl_32392 : CNF.NClause := [(81,false),(28,true),(9,true),(23,true),(15,true),(1,true)]
theorem der_32392 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32392 :=
  CNF.rup_sound cl_32392 [cl_1276,cl_23681] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1276 v h) (hints_cons _ _ _ (der_23681 v h) (by intro d hd; cases hd)))
def cl_32393 : CNF.NClause := [(81,false),(28,true),(1,true),(23,true),(12,true),(15,true)]
theorem der_32393 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32393 :=
  CNF.rup_sound cl_32393 [cl_1278,cl_23681] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1278 v h) (hints_cons _ _ _ (der_23681 v h) (by intro d hd; cases hd)))
def cl_32394 : CNF.NClause := [(81,false),(28,true),(9,true),(12,true),(15,true),(23,true)]
theorem der_32394 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32394 :=
  CNF.rup_sound cl_32394 [cl_1279,cl_23681] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_1279 v h) (hints_cons _ _ _ (der_23681 v h) (by intro d hd; cases hd)))
def cl_32395 : CNF.NClause := [(75,false),(10,true),(22,true),(9,true),(3,true),(16,true)]
theorem der_32395 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32395 :=
  CNF.rup_sound cl_32395 [cl_864,cl_23682] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_864 v h) (hints_cons _ _ _ (der_23682 v h) (by intro d hd; cases hd)))
def cl_32396 : CNF.NClause := [(75,false),(26,true),(9,true),(3,true),(10,true),(16,true)]
theorem der_32396 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32396 :=
  CNF.rup_sound cl_32396 [cl_880,cl_23682] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_880 v h) (hints_cons _ _ _ (der_23682 v h) (by intro d hd; cases hd)))
def cl_32397 : CNF.NClause := [(75,false),(26,true),(9,true),(3,true),(10,true),(22,true)]
theorem der_32397 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32397 :=
  CNF.rup_sound cl_32397 [cl_888,cl_23682] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_888 v h) (hints_cons _ _ _ (der_23682 v h) (by intro d hd; cases hd)))
def cl_32398 : CNF.NClause := [(75,false),(3,true),(26,true),(16,true),(22,true),(9,true)]
theorem der_32398 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32398 :=
  CNF.rup_sound cl_32398 [cl_892,cl_23682] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_892 v h) (hints_cons _ _ _ (der_23682 v h) (by intro d hd; cases hd)))
def cl_32399 : CNF.NClause := [(75,false),(10,true),(22,true),(26,true),(9,true),(16,true)]
theorem der_32399 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32399 :=
  CNF.rup_sound cl_32399 [cl_895,cl_23682] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_895 v h) (hints_cons _ _ _ (der_23682 v h) (by intro d hd; cases hd)))
def cl_32402 : CNF.NClause := [(69,false),(9,true),(11,true),(2,true),(18,true),(20,true)]
theorem der_32402 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32402 :=
  CNF.rup_sound cl_32402 [cl_480,cl_23688] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_480 v h) (hints_cons _ _ _ (der_23688 v h) (by intro d hd; cases hd)))
def cl_32403 : CNF.NClause := [(69,false),(18,true),(11,true),(27,true),(9,true),(2,true)]
theorem der_32403 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32403 :=
  CNF.rup_sound cl_32403 [cl_496,cl_23688] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_496 v h) (hints_cons _ _ _ (der_23688 v h) (by intro d hd; cases hd)))
def cl_32404 : CNF.NClause := [(69,false),(9,true),(27,true),(2,true),(11,true),(20,true)]
theorem der_32404 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32404 :=
  CNF.rup_sound cl_32404 [cl_504,cl_23688] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_504 v h) (hints_cons _ _ _ (der_23688 v h) (by intro d hd; cases hd)))
def cl_32405 : CNF.NClause := [(69,false),(9,true),(27,true),(18,true),(11,true),(20,true)]
theorem der_32405 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32405 :=
  CNF.rup_sound cl_32405 [cl_511,cl_23688] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_511 v h) (hints_cons _ _ _ (der_23688 v h) (by intro d hd; cases hd)))
def cl_32406 : CNF.NClause := [(86,false),(53,false),(90,false),(67,false),(22,true),(64,false)]
theorem der_32406 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32406 :=
  CNF.rup_sound cl_32406 [cl_26768,cl_26767] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26768 v h) (hints_cons _ _ _ (der_26767 v h) (by intro d hd; cases hd)))
def cl_32407 : CNF.NClause := [(78,false),(53,false),(90,false),(67,false),(22,true),(64,false)]
theorem der_32407 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32407 :=
  CNF.rup_sound cl_32407 [cl_26770,cl_26769] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26770 v h) (hints_cons _ _ _ (der_26769 v h) (by intro d hd; cases hd)))
def cl_32408 : CNF.NClause := [(75,false),(53,false),(90,false),(67,false),(64,false),(22,true)]
theorem der_32408 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32408 :=
  CNF.rup_sound cl_32408 [cl_26771,cl_26769] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26771 v h) (hints_cons _ _ _ (der_26769 v h) (by intro d hd; cases hd)))
def cl_32409 : CNF.NClause := [(53,false),(67,false),(78,true),(90,false),(22,true),(64,false)]
theorem der_32409 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32409 :=
  CNF.rup_sound cl_32409 [cl_26772,cl_32408] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26772 v h) (hints_cons _ _ _ (der_32408 v h) (by intro d hd; cases hd)))
def cl_32410 : CNF.NClause := [(78,false),(53,false),(67,false),(64,false),(22,true),(86,false)]
theorem der_32410 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32410 :=
  CNF.rup_sound cl_32410 [cl_26774,cl_26773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26774 v h) (hints_cons _ _ _ (der_26773 v h) (by intro d hd; cases hd)))
def cl_32411 : CNF.NClause := [(53,false),(22,true),(67,false),(64,false),(86,false),(75,false)]
theorem der_32411 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32411 :=
  CNF.rup_sound cl_32411 [cl_26775,cl_26773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26775 v h) (hints_cons _ _ _ (der_26773 v h) (by intro d hd; cases hd)))
def cl_32412 : CNF.NClause := [(86,false),(53,false),(67,false),(64,false),(22,true),(90,true)]
theorem der_32412 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32412 :=
  CNF.rup_sound cl_32412 [cl_26776,cl_32411] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26776 v h) (hints_cons _ _ _ (der_32411 v h) (by intro d hd; cases hd)))
def cl_32413 : CNF.NClause := [(53,false),(67,false),(22,true),(64,false),(78,false),(75,false)]
theorem der_32413 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32413 :=
  CNF.rup_sound cl_32413 [cl_26777,cl_26773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26777 v h) (hints_cons _ _ _ (der_26773 v h) (by intro d hd; cases hd)))
def cl_32414 : CNF.NClause := [(53,false),(22,true),(67,false),(64,false),(78,false),(90,true)]
theorem der_32414 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32414 :=
  CNF.rup_sound cl_32414 [cl_26778,cl_32413] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26778 v h) (hints_cons _ _ _ (der_32413 v h) (by intro d hd; cases hd)))
def cl_32416 : CNF.NClause := [(90,true),(53,false),(86,true),(67,false),(22,true),(64,false)]
theorem der_32416 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32416 :=
  CNF.rup_sound cl_32416 [cl_26780,cl_32414] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26780 v h) (hints_cons _ _ _ (der_32414 v h) (by intro d hd; cases hd)))
def cl_32417 : CNF.NClause := [(40,false),(82,false),(63,false),(9,true),(88,false),(81,false)]
theorem der_32417 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32417 :=
  CNF.rup_sound cl_32417 [cl_26783,cl_26781] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26783 v h) (hints_cons _ _ _ (der_26781 v h) (by intro d hd; cases hd)))
def cl_32418 : CNF.NClause := [(40,false),(75,false),(63,false),(88,false),(9,true),(82,false)]
theorem der_32418 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32418 :=
  CNF.rup_sound cl_32418 [cl_26785,cl_26781] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26785 v h) (hints_cons _ _ _ (der_26781 v h) (by intro d hd; cases hd)))
def cl_32419 : CNF.NClause := [(40,false),(69,false),(63,false),(88,false),(9,true),(82,false)]
theorem der_32419 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32419 :=
  CNF.rup_sound cl_32419 [cl_26786,cl_26784] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26786 v h) (hints_cons _ _ _ (der_26784 v h) (by intro d hd; cases hd)))
def cl_32420 : CNF.NClause := [(40,false),(88,false),(75,true),(9,true),(63,false),(82,false)]
theorem der_32420 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32420 :=
  CNF.rup_sound cl_32420 [cl_26787,cl_32417] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26787 v h) (hints_cons _ _ _ (der_32417 v h) (by intro d hd; cases hd)))
def cl_32421 : CNF.NClause := [(40,false),(81,false),(75,true),(63,false),(9,true),(88,false)]
theorem der_32421 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32421 :=
  CNF.rup_sound cl_32421 [cl_26790,cl_32417] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26790 v h) (hints_cons _ _ _ (der_32417 v h) (by intro d hd; cases hd)))
def cl_32422 : CNF.NClause := [(40,false),(75,false),(81,true),(63,false),(88,false),(9,true)]
theorem der_32422 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32422 :=
  CNF.rup_sound cl_32422 [cl_26792,cl_32418] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26792 v h) (hints_cons _ _ _ (der_32418 v h) (by intro d hd; cases hd)))
def cl_32423 : CNF.NClause := [(40,false),(69,false),(81,true),(63,false),(88,false),(9,true)]
theorem der_32423 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32423 :=
  CNF.rup_sound cl_32423 [cl_26793,cl_32419] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26793 v h) (hints_cons _ _ _ (der_32419 v h) (by intro d hd; cases hd)))
def cl_32424 : CNF.NClause := [(40,false),(88,false),(69,true),(75,true),(9,true),(63,false)]
theorem der_32424 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32424 :=
  CNF.rup_sound cl_32424 [cl_26794,cl_32420] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26794 v h) (hints_cons _ _ _ (der_32420 v h) (by intro d hd; cases hd)))
def cl_32425 : CNF.NClause := [(40,false),(81,false),(75,true),(63,false),(9,true),(82,false)]
theorem der_32425 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32425 :=
  CNF.rup_sound cl_32425 [cl_26797,cl_32421] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26797 v h) (hints_cons _ _ _ (der_32421 v h) (by intro d hd; cases hd)))
def cl_32427 : CNF.NClause := [(40,false),(69,false),(81,true),(63,false),(82,false),(9,true)]
theorem der_32427 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32427 :=
  CNF.rup_sound cl_32427 [cl_26800,cl_32419] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26800 v h) (hints_cons _ _ _ (der_32419 v h) (by intro d hd; cases hd)))
def cl_32428 : CNF.NClause := [(40,false),(82,false),(81,true),(9,true),(63,false),(88,true)]
theorem der_32428 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32428 :=
  CNF.rup_sound cl_32428 [cl_26801,cl_32427] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26801 v h) (hints_cons _ _ _ (der_32427 v h) (by intro d hd; cases hd)))
def cl_32429 : CNF.NClause := [(40,false),(81,false),(69,true),(63,false),(75,false),(9,true)]
theorem der_32429 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32429 :=
  CNF.rup_sound cl_32429 [cl_26802,cl_26795] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26802 v h) (hints_cons _ _ _ (der_26795 v h) (by intro d hd; cases hd)))
def cl_32430 : CNF.NClause := [(40,false),(75,true),(63,false),(69,false),(81,false),(9,true)]
theorem der_32430 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32430 :=
  CNF.rup_sound cl_32430 [cl_26803,cl_26789] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26803 v h) (hints_cons _ _ _ (der_26789 v h) (by intro d hd; cases hd)))
def cl_32431 : CNF.NClause := [(40,false),(81,false),(69,true),(75,true),(9,true),(63,false)]
theorem der_32431 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32431 :=
  CNF.rup_sound cl_32431 [cl_26804,cl_32425] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26804 v h) (hints_cons _ _ _ (der_32425 v h) (by intro d hd; cases hd)))
def cl_32433 : CNF.NClause := [(40,false),(88,true),(81,true),(63,false),(75,false),(9,true)]
theorem der_32433 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32433 :=
  CNF.rup_sound cl_32433 [cl_26806,cl_32428] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26806 v h) (hints_cons _ _ _ (der_32428 v h) (by intro d hd; cases hd)))
def cl_32435 : CNF.NClause := [(40,false),(69,true),(75,true),(9,true),(63,false),(82,true)]
theorem der_32435 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32435 :=
  CNF.rup_sound cl_32435 [cl_26808,cl_32431] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26808 v h) (hints_cons _ _ _ (der_32431 v h) (by intro d hd; cases hd)))
def cl_32436 : CNF.NClause := [(45,false),(86,false),(70,true),(63,false),(14,true),(89,false)]
theorem der_32436 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32436 :=
  CNF.rup_sound cl_32436 [cl_26812,cl_26811] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26812 v h) (hints_cons _ _ _ (der_26811 v h) (by intro d hd; cases hd)))
def cl_32437 : CNF.NClause := [(45,false),(79,false),(63,false),(72,false),(89,false),(14,true)]
theorem der_32437 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32437 :=
  CNF.rup_sound cl_32437 [cl_26813,cl_26809] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26813 v h) (hints_cons _ _ _ (der_26809 v h) (by intro d hd; cases hd)))
def cl_32438 : CNF.NClause := [(45,false),(79,false),(70,true),(63,false),(89,false),(14,true)]
theorem der_32438 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32438 :=
  CNF.rup_sound cl_32438 [cl_26814,cl_26810] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26814 v h) (hints_cons _ _ _ (der_26810 v h) (by intro d hd; cases hd)))
def cl_32440 : CNF.NClause := [(45,false),(89,false),(70,true),(86,true),(14,true),(63,false)]
theorem der_32440 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32440 :=
  CNF.rup_sound cl_32440 [cl_26816,cl_32438] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26816 v h) (hints_cons _ _ _ (der_32438 v h) (by intro d hd; cases hd)))
def cl_32441 : CNF.NClause := [(45,false),(70,true),(63,false),(79,false),(86,false),(14,true)]
theorem der_32441 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32441 :=
  CNF.rup_sound cl_32441 [cl_26818,cl_26810] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26818 v h) (hints_cons _ _ _ (der_26810 v h) (by intro d hd; cases hd)))
def cl_32442 : CNF.NClause := [(45,false),(86,false),(70,true),(63,false),(72,false),(14,true)]
theorem der_32442 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32442 :=
  CNF.rup_sound cl_32442 [cl_26819,cl_26811] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26819 v h) (hints_cons _ _ _ (der_26811 v h) (by intro d hd; cases hd)))
def cl_32443 : CNF.NClause := [(45,false),(86,false),(70,true),(79,true),(14,true),(63,false)]
theorem der_32443 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32443 :=
  CNF.rup_sound cl_32443 [cl_26820,cl_32442] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26820 v h) (hints_cons _ _ _ (der_32442 v h) (by intro d hd; cases hd)))
def cl_32445 : CNF.NClause := [(45,false),(70,true),(86,true),(63,false),(79,false),(14,true)]
theorem der_32445 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32445 :=
  CNF.rup_sound cl_32445 [cl_26822,cl_32438] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26822 v h) (hints_cons _ _ _ (der_32438 v h) (by intro d hd; cases hd)))
def cl_32446 : CNF.NClause := [(45,false),(72,false),(70,true),(79,true),(14,true),(63,false)]
theorem der_32446 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32446 :=
  CNF.rup_sound cl_32446 [cl_26823,cl_32442] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26823 v h) (hints_cons _ _ _ (der_32442 v h) (by intro d hd; cases hd)))
def cl_32447 : CNF.NClause := [(45,false),(70,true),(86,true),(79,true),(14,true),(63,false)]
theorem der_32447 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32447 :=
  CNF.rup_sound cl_32447 [cl_26824,cl_32446] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26824 v h) (hints_cons _ _ _ (der_32446 v h) (by intro d hd; cases hd)))
def cl_32448 : CNF.NClause := [(50,false),(71,false),(77,true),(63,false),(85,false),(74,false)]
theorem der_32448 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32448 :=
  CNF.rup_sound cl_32448 [cl_26825,cl_32385] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26825 v h) (hints_cons _ _ _ (der_32385 v h) (by intro d hd; cases hd)))
def cl_32449 : CNF.NClause := [(58,false),(69,true),(85,false),(89,false),(78,false),(76,false)]
theorem der_32449 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32449 :=
  CNF.rup_sound cl_32449 [cl_26830,cl_26828] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26830 v h) (hints_cons _ _ _ (der_26828 v h) (by intro d hd; cases hd)))
def cl_32450 : CNF.NClause := [(58,false),(62,true),(85,false),(89,false),(78,false),(69,false)]
theorem der_32450 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32450 :=
  CNF.rup_sound cl_32450 [cl_26833,cl_26827] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26833 v h) (hints_cons _ _ _ (der_26827 v h) (by intro d hd; cases hd)))
def cl_32451 : CNF.NClause := [(58,false),(62,false),(85,false),(27,true),(89,false),(78,false)]
theorem der_32451 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32451 :=
  CNF.rup_sound cl_32451 [cl_26835,cl_26831] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26835 v h) (hints_cons _ _ _ (der_26831 v h) (by intro d hd; cases hd)))
def cl_32452 : CNF.NClause := [(58,false),(69,true),(27,false),(85,false),(89,false),(78,false)]
theorem der_32452 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32452 :=
  CNF.rup_sound cl_32452 [cl_26836,cl_26834] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26836 v h) (hints_cons _ _ _ (der_26834 v h) (by intro d hd; cases hd)))
def cl_32453 : CNF.NClause := [(58,false),(69,true),(62,true),(85,false),(89,false),(78,false)]
theorem der_32453 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32453 :=
  CNF.rup_sound cl_32453 [cl_26837,cl_32449] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26837 v h) (hints_cons _ _ _ (der_32449 v h) (by intro d hd; cases hd)))
def cl_32454 : CNF.NClause := [(58,false),(85,false),(27,true),(89,false),(69,false),(76,false)]
theorem der_32454 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32454 :=
  CNF.rup_sound cl_32454 [cl_26840,cl_26826] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26840 v h) (hints_cons _ _ _ (der_26826 v h) (by intro d hd; cases hd)))
def cl_32455 : CNF.NClause := [(58,false),(76,false),(85,false),(89,false),(27,true),(62,false)]
theorem der_32455 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32455 :=
  CNF.rup_sound cl_32455 [cl_26842,cl_32451] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26842 v h) (hints_cons _ _ _ (der_32451 v h) (by intro d hd; cases hd)))
def cl_32456 : CNF.NClause := [(58,false),(78,true),(27,false),(85,false),(89,false),(76,false)]
theorem der_32456 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32456 :=
  CNF.rup_sound cl_32456 [cl_26843,cl_26841] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26843 v h) (hints_cons _ _ _ (der_26841 v h) (by intro d hd; cases hd)))
def cl_32457 : CNF.NClause := [(58,false),(76,false),(78,true),(85,false),(27,true),(89,false)]
theorem der_32457 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32457 :=
  CNF.rup_sound cl_32457 [cl_26844,cl_32455] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26844 v h) (hints_cons _ _ _ (der_32455 v h) (by intro d hd; cases hd)))
def cl_32458 : CNF.NClause := [(58,false),(76,true),(27,false),(85,false),(89,false),(69,false)]
theorem der_32458 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32458 :=
  CNF.rup_sound cl_32458 [cl_26847,cl_26845] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26847 v h) (hints_cons _ _ _ (der_26845 v h) (by intro d hd; cases hd)))
def cl_32459 : CNF.NClause := [(58,false),(69,false),(62,true),(85,false),(27,true),(89,false)]
theorem der_32459 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32459 :=
  CNF.rup_sound cl_32459 [cl_26848,cl_32450] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26848 v h) (hints_cons _ _ _ (der_32450 v h) (by intro d hd; cases hd)))
def cl_32460 : CNF.NClause := [(58,false),(78,true),(27,false),(85,false),(89,false),(62,false)]
theorem der_32460 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32460 :=
  CNF.rup_sound cl_32460 [cl_26849,cl_32456] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26849 v h) (hints_cons _ _ _ (der_32456 v h) (by intro d hd; cases hd)))
def cl_32461 : CNF.NClause := [(58,false),(85,false),(78,true),(76,true),(89,false),(62,false)]
theorem der_32461 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32461 :=
  CNF.rup_sound cl_32461 [cl_26850,cl_32460] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26850 v h) (hints_cons _ _ _ (der_32460 v h) (by intro d hd; cases hd)))
def cl_32462 : CNF.NClause := [(58,false),(76,true),(62,true),(27,false),(85,false),(89,false)]
theorem der_32462 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32462 :=
  CNF.rup_sound cl_32462 [cl_26851,cl_32458] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26851 v h) (hints_cons _ _ _ (der_32458 v h) (by intro d hd; cases hd)))
def cl_32463 : CNF.NClause := [(58,false),(78,true),(69,true),(27,true),(85,false),(89,false)]
theorem der_32463 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32463 :=
  CNF.rup_sound cl_32463 [cl_26852,cl_32457] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26852 v h) (hints_cons _ _ _ (der_32457 v h) (by intro d hd; cases hd)))
def cl_32464 : CNF.NClause := [(58,false),(76,false),(69,true),(89,false),(62,false),(78,false)]
theorem der_32464 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32464 :=
  CNF.rup_sound cl_32464 [cl_26857,cl_26856] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26857 v h) (hints_cons _ _ _ (der_26856 v h) (by intro d hd; cases hd)))
def cl_32466 : CNF.NClause := [(58,false),(69,true),(62,true),(89,false),(78,false),(76,false)]
theorem der_32466 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32466 :=
  CNF.rup_sound cl_32466 [cl_26859,cl_32449] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26859 v h) (hints_cons _ _ _ (der_32449 v h) (by intro d hd; cases hd)))
def cl_32467 : CNF.NClause := [(58,false),(78,false),(76,true),(89,false),(62,false),(69,false)]
theorem der_32467 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32467 :=
  CNF.rup_sound cl_32467 [cl_26861,cl_26860] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26861 v h) (hints_cons _ _ _ (der_26860 v h) (by intro d hd; cases hd)))
def cl_32468 : CNF.NClause := [(58,false),(76,true),(27,false),(89,false),(78,false),(69,false)]
theorem der_32468 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32468 :=
  CNF.rup_sound cl_32468 [cl_26862,cl_32467] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26862 v h) (hints_cons _ _ _ (der_32467 v h) (by intro d hd; cases hd)))
def cl_32469 : CNF.NClause := [(58,false),(69,false),(76,true),(89,false),(78,false),(85,true)]
theorem der_32469 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32469 :=
  CNF.rup_sound cl_32469 [cl_26863,cl_32468] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26863 v h) (hints_cons _ _ _ (der_32468 v h) (by intro d hd; cases hd)))
def cl_32470 : CNF.NClause := [(58,false),(78,false),(69,true),(89,false),(27,true),(62,false)]
theorem der_32470 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32470 :=
  CNF.rup_sound cl_32470 [cl_26865,cl_32451] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26865 v h) (hints_cons _ _ _ (der_32451 v h) (by intro d hd; cases hd)))
def cl_32471 : CNF.NClause := [(58,false),(69,true),(62,true),(27,false),(89,false),(78,false)]
theorem der_32471 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32471 :=
  CNF.rup_sound cl_32471 [cl_26866,cl_32453] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26866 v h) (hints_cons _ _ _ (der_32453 v h) (by intro d hd; cases hd)))
def cl_32472 : CNF.NClause := [(58,false),(78,false),(69,true),(62,true),(89,false),(85,true)]
theorem der_32472 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32472 :=
  CNF.rup_sound cl_32472 [cl_26867,cl_32471] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26867 v h) (hints_cons _ _ _ (der_32471 v h) (by intro d hd; cases hd)))
def cl_32473 : CNF.NClause := [(58,false),(78,true),(27,false),(89,false),(62,false),(76,false)]
theorem der_32473 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32473 :=
  CNF.rup_sound cl_32473 [cl_26872,cl_32460] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26872 v h) (hints_cons _ _ _ (der_32460 v h) (by intro d hd; cases hd)))
def cl_32474 : CNF.NClause := [(58,false),(69,true),(89,false),(62,false),(76,false),(85,true)]
theorem der_32474 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32474 :=
  CNF.rup_sound cl_32474 [cl_26873,cl_32464] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26873 v h) (hints_cons _ _ _ (der_32464 v h) (by intro d hd; cases hd)))
def cl_32475 : CNF.NClause := [(58,false),(69,true),(27,false),(89,false),(76,false),(85,true)]
theorem der_32475 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32475 :=
  CNF.rup_sound cl_32475 [cl_26874,cl_32474] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26874 v h) (hints_cons _ _ _ (der_32474 v h) (by intro d hd; cases hd)))
def cl_32476 : CNF.NClause := [(58,false),(76,false),(69,true),(62,true),(89,false),(85,true)]
theorem der_32476 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32476 :=
  CNF.rup_sound cl_32476 [cl_26875,cl_32475] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26875 v h) (hints_cons _ _ _ (der_32475 v h) (by intro d hd; cases hd)))
def cl_32477 : CNF.NClause := [(58,false),(78,true),(27,false),(89,false),(62,false),(69,false)]
theorem der_32477 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32477 :=
  CNF.rup_sound cl_32477 [cl_26876,cl_32473] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26876 v h) (hints_cons _ _ _ (der_32473 v h) (by intro d hd; cases hd)))
def cl_32478 : CNF.NClause := [(58,false),(69,false),(78,true),(76,true),(89,false),(62,false)]
theorem der_32478 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32478 :=
  CNF.rup_sound cl_32478 [cl_26877,cl_32477] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26877 v h) (hints_cons _ _ _ (der_32477 v h) (by intro d hd; cases hd)))
def cl_32479 : CNF.NClause := [(58,false),(78,true),(27,false),(89,false),(69,false),(85,true)]
theorem der_32479 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32479 :=
  CNF.rup_sound cl_32479 [cl_26878,cl_32477] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26878 v h) (hints_cons _ _ _ (der_32477 v h) (by intro d hd; cases hd)))
def cl_32480 : CNF.NClause := [(58,false),(69,false),(76,true),(62,true),(89,false),(27,true)]
theorem der_32480 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32480 :=
  CNF.rup_sound cl_32480 [cl_26879,cl_32459] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26879 v h) (hints_cons _ _ _ (der_32459 v h) (by intro d hd; cases hd)))
def cl_32481 : CNF.NClause := [(58,false),(76,true),(27,false),(89,false),(62,false),(85,true)]
theorem der_32481 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32481 :=
  CNF.rup_sound cl_32481 [cl_26880,cl_26864] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26880 v h) (hints_cons _ _ _ (der_26864 v h) (by intro d hd; cases hd)))
def cl_32482 : CNF.NClause := [(58,false),(76,true),(78,true),(27,true),(89,false),(62,false)]
theorem der_32482 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32482 :=
  CNF.rup_sound cl_32482 [cl_26881,cl_32478] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26881 v h) (hints_cons _ _ _ (der_32478 v h) (by intro d hd; cases hd)))
def cl_32484 : CNF.NClause := [(58,false),(78,true),(76,true),(27,true),(89,false),(85,true)]
theorem der_32484 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32484 :=
  CNF.rup_sound cl_32484 [cl_26883,cl_32482] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26883 v h) (hints_cons _ _ _ (der_32482 v h) (by intro d hd; cases hd)))
def cl_32485 : CNF.NClause := [(58,false),(76,false),(85,false),(78,false),(69,false),(27,true)]
theorem der_32485 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32485 :=
  CNF.rup_sound cl_32485 [cl_26886,cl_26826] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26886 v h) (hints_cons _ _ _ (der_26826 v h) (by intro d hd; cases hd)))
def cl_32486 : CNF.NClause := [(58,false),(76,false),(85,false),(62,false),(78,false),(27,true)]
theorem der_32486 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32486 :=
  CNF.rup_sound cl_32486 [cl_26888,cl_26884] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26888 v h) (hints_cons _ _ _ (der_26884 v h) (by intro d hd; cases hd)))
def cl_32487 : CNF.NClause := [(58,false),(69,true),(27,false),(85,false),(78,false),(76,false)]
theorem der_32487 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32487 :=
  CNF.rup_sound cl_32487 [cl_26889,cl_26887] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26889 v h) (hints_cons _ _ _ (der_26887 v h) (by intro d hd; cases hd)))
def cl_32488 : CNF.NClause := [(58,false),(69,true),(62,true),(85,false),(78,false),(76,false)]
theorem der_32488 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32488 :=
  CNF.rup_sound cl_32488 [cl_26890,cl_32487] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26890 v h) (hints_cons _ _ _ (der_32487 v h) (by intro d hd; cases hd)))
def cl_32489 : CNF.NClause := [(58,false),(78,false),(85,false),(27,true),(62,false),(69,false)]
theorem der_32489 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32489 :=
  CNF.rup_sound cl_32489 [cl_26892,cl_26831] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26892 v h) (hints_cons _ _ _ (der_26831 v h) (by intro d hd; cases hd)))
def cl_32490 : CNF.NClause := [(58,false),(78,false),(76,true),(85,false),(27,true),(69,false)]
theorem der_32490 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32490 :=
  CNF.rup_sound cl_32490 [cl_26894,cl_32489] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26894 v h) (hints_cons _ _ _ (der_32489 v h) (by intro d hd; cases hd)))
def cl_32491 : CNF.NClause := [(58,false),(69,true),(27,false),(85,false),(62,false),(78,false)]
theorem der_32491 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32491 :=
  CNF.rup_sound cl_32491 [cl_26895,cl_32487] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26895 v h) (hints_cons _ _ _ (der_32487 v h) (by intro d hd; cases hd)))
def cl_32492 : CNF.NClause := [(58,false),(85,false),(76,true),(27,true),(62,false),(78,false)]
theorem der_32492 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32492 :=
  CNF.rup_sound cl_32492 [cl_26896,cl_32490] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26896 v h) (hints_cons _ _ _ (der_32490 v h) (by intro d hd; cases hd)))
def cl_32494 : CNF.NClause := [(58,false),(69,true),(76,true),(62,true),(85,false),(78,false)]
theorem der_32494 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32494 :=
  CNF.rup_sound cl_32494 [cl_26898,cl_32453] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26898 v h) (hints_cons _ _ _ (der_32453 v h) (by intro d hd; cases hd)))
def cl_32495 : CNF.NClause := [(58,false),(85,false),(27,true),(62,false),(69,false),(76,false)]
theorem der_32495 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32495 :=
  CNF.rup_sound cl_32495 [cl_26900,cl_32454] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26900 v h) (hints_cons _ _ _ (der_32454 v h) (by intro d hd; cases hd)))
def cl_32496 : CNF.NClause := [(58,false),(78,true),(27,false),(85,false),(69,false),(76,false)]
theorem der_32496 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32496 :=
  CNF.rup_sound cl_32496 [cl_26901,cl_26899] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26901 v h) (hints_cons _ _ _ (der_26899 v h) (by intro d hd; cases hd)))
def cl_32498 : CNF.NClause := [(58,false),(69,true),(27,false),(85,false),(76,false),(89,true)]
theorem der_32498 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32498 :=
  CNF.rup_sound cl_32498 [cl_26905,cl_32487] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26905 v h) (hints_cons _ _ _ (der_32487 v h) (by intro d hd; cases hd)))
def cl_32499 : CNF.NClause := [(58,false),(85,false),(69,true),(62,true),(27,true),(76,false)]
theorem der_32499 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32499 :=
  CNF.rup_sound cl_32499 [cl_26906,cl_32488] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26906 v h) (hints_cons _ _ _ (der_32488 v h) (by intro d hd; cases hd)))
def cl_32500 : CNF.NClause := [(58,false),(78,true),(27,false),(85,false),(62,false),(69,false)]
theorem der_32500 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32500 :=
  CNF.rup_sound cl_32500 [cl_26907,cl_32477] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26907 v h) (hints_cons _ _ _ (der_32477 v h) (by intro d hd; cases hd)))
def cl_32501 : CNF.NClause := [(58,false),(27,true),(76,true),(85,false),(62,false),(69,false)]
theorem der_32501 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32501 :=
  CNF.rup_sound cl_32501 [cl_26908,cl_32489] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26908 v h) (hints_cons _ _ _ (der_32489 v h) (by intro d hd; cases hd)))
def cl_32502 : CNF.NClause := [(58,false),(78,true),(27,false),(85,false),(69,false),(89,true)]
theorem der_32502 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32502 :=
  CNF.rup_sound cl_32502 [cl_26909,cl_32500] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26909 v h) (hints_cons _ _ _ (der_32500 v h) (by intro d hd; cases hd)))
def cl_32504 : CNF.NClause := [(58,false),(78,true),(27,false),(85,false),(62,false),(89,true)]
theorem der_32504 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32504 :=
  CNF.rup_sound cl_32504 [cl_26911,cl_32500] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26911 v h) (hints_cons _ _ _ (der_32500 v h) (by intro d hd; cases hd)))
def cl_32505 : CNF.NClause := [(58,false),(76,true),(69,true),(27,true),(85,false),(62,false)]
theorem der_32505 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32505 :=
  CNF.rup_sound cl_32505 [cl_26912,cl_32492] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26912 v h) (hints_cons _ _ _ (der_32492 v h) (by intro d hd; cases hd)))
def cl_32507 : CNF.NClause := [(58,false),(85,true),(27,false),(78,false),(69,false),(76,false)]
theorem der_32507 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32507 :=
  CNF.rup_sound cl_32507 [cl_26917,cl_26915] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26917 v h) (hints_cons _ _ _ (der_26915 v h) (by intro d hd; cases hd)))
def cl_32508 : CNF.NClause := [(58,false),(62,true),(78,false),(69,false),(76,false),(27,true)]
theorem der_32508 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32508 :=
  CNF.rup_sound cl_32508 [cl_26918,cl_32485] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26918 v h) (hints_cons _ _ _ (der_32485 v h) (by intro d hd; cases hd)))
def cl_32509 : CNF.NClause := [(58,false),(69,true),(27,false),(62,false),(78,false),(76,false)]
theorem der_32509 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32509 :=
  CNF.rup_sound cl_32509 [cl_26919,cl_32487] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26919 v h) (hints_cons _ _ _ (der_32487 v h) (by intro d hd; cases hd)))
def cl_32510 : CNF.NClause := [(58,false),(69,true),(62,false),(78,false),(76,false),(85,true)]
theorem der_32510 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32510 :=
  CNF.rup_sound cl_32510 [cl_26920,cl_32474] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26920 v h) (hints_cons _ _ _ (der_32474 v h) (by intro d hd; cases hd)))
def cl_32511 : CNF.NClause := [(58,false),(69,true),(62,true),(27,false),(78,false),(76,false)]
theorem der_32511 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32511 :=
  CNF.rup_sound cl_32511 [cl_26921,cl_32487] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26921 v h) (hints_cons _ _ _ (der_32487 v h) (by intro d hd; cases hd)))
def cl_32512 : CNF.NClause := [(58,false),(69,true),(62,true),(78,false),(76,false),(27,true)]
theorem der_32512 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32512 :=
  CNF.rup_sound cl_32512 [cl_26922,cl_32499] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26922 v h) (hints_cons _ _ _ (der_32499 v h) (by intro d hd; cases hd)))
def cl_32513 : CNF.NClause := [(58,false),(76,true),(27,false),(62,false),(78,false),(69,false)]
theorem der_32513 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32513 :=
  CNF.rup_sound cl_32513 [cl_26923,cl_32467] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26923 v h) (hints_cons _ _ _ (der_32467 v h) (by intro d hd; cases hd)))
def cl_32514 : CNF.NClause := [(58,false),(78,false),(76,true),(62,false),(27,true),(69,false)]
theorem der_32514 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32514 :=
  CNF.rup_sound cl_32514 [cl_26924,cl_32489] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26924 v h) (hints_cons _ _ _ (der_32489 v h) (by intro d hd; cases hd)))
def cl_32515 : CNF.NClause := [(58,false),(76,true),(62,true),(27,false),(78,false),(69,false)]
theorem der_32515 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32515 :=
  CNF.rup_sound cl_32515 [cl_26925,cl_26893] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26925 v h) (hints_cons _ _ _ (der_26893 v h) (by intro d hd; cases hd)))
def cl_32516 : CNF.NClause := [(58,false),(78,false),(76,true),(27,true),(69,false),(85,true)]
theorem der_32516 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32516 :=
  CNF.rup_sound cl_32516 [cl_26926,cl_32514] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26926 v h) (hints_cons _ _ _ (der_32514 v h) (by intro d hd; cases hd)))
def cl_32517 : CNF.NClause := [(58,false),(69,true),(27,false),(62,false),(78,false),(89,true)]
theorem der_32517 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32517 :=
  CNF.rup_sound cl_32517 [cl_26927,cl_32491] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26927 v h) (hints_cons _ _ _ (der_32491 v h) (by intro d hd; cases hd)))
def cl_32518 : CNF.NClause := [(58,false),(78,false),(76,true),(62,false),(27,true),(89,true)]
theorem der_32518 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32518 :=
  CNF.rup_sound cl_32518 [cl_26928,cl_32492] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26928 v h) (hints_cons _ _ _ (der_32492 v h) (by intro d hd; cases hd)))
def cl_32519 : CNF.NClause := [(58,false),(69,true),(76,true),(62,true),(27,false),(78,false)]
theorem der_32519 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32519 :=
  CNF.rup_sound cl_32519 [cl_26929,cl_32471] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26929 v h) (hints_cons _ _ _ (der_32471 v h) (by intro d hd; cases hd)))
def cl_32520 : CNF.NClause := [(58,false),(78,false),(69,true),(62,true),(27,true),(85,true)]
theorem der_32520 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32520 :=
  CNF.rup_sound cl_32520 [cl_26930,cl_32472] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26930 v h) (hints_cons _ _ _ (der_32472 v h) (by intro d hd; cases hd)))
def cl_32521 : CNF.NClause := [(58,false),(78,true),(27,false),(62,false),(69,false),(76,false)]
theorem der_32521 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32521 :=
  CNF.rup_sound cl_32521 [cl_26931,cl_32477] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26931 v h) (hints_cons _ _ _ (der_32477 v h) (by intro d hd; cases hd)))
def cl_32522 : CNF.NClause := [(58,false),(62,false),(89,true),(69,false),(76,false),(27,true)]
theorem der_32522 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32522 :=
  CNF.rup_sound cl_32522 [cl_26932,cl_32495] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26932 v h) (hints_cons _ _ _ (der_32495 v h) (by intro d hd; cases hd)))
def cl_32523 : CNF.NClause := [(58,false),(78,true),(27,false),(69,false),(76,false),(85,true)]
theorem der_32523 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32523 :=
  CNF.rup_sound cl_32523 [cl_26933,cl_32521] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26933 v h) (hints_cons _ _ _ (der_32521 v h) (by intro d hd; cases hd)))
def cl_32524 : CNF.NClause := [(58,false),(85,true),(78,true),(62,true),(69,false),(76,false)]
theorem der_32524 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32524 :=
  CNF.rup_sound cl_32524 [cl_26934,cl_32523] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26934 v h) (hints_cons _ _ _ (der_32523 v h) (by intro d hd; cases hd)))
def cl_32526 : CNF.NClause := [(58,false),(76,false),(69,true),(62,false),(27,true),(85,true)]
theorem der_32526 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32526 :=
  CNF.rup_sound cl_32526 [cl_26936,cl_32510] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26936 v h) (hints_cons _ _ _ (der_32510 v h) (by intro d hd; cases hd)))
def cl_32527 : CNF.NClause := [(58,false),(78,true),(69,true),(27,false),(76,false),(85,true)]
theorem der_32527 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32527 :=
  CNF.rup_sound cl_32527 [cl_26937,cl_32475] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26937 v h) (hints_cons _ _ _ (der_32475 v h) (by intro d hd; cases hd)))
def cl_32528 : CNF.NClause := [(58,false),(69,true),(62,true),(76,false),(27,true),(89,true)]
theorem der_32528 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32528 :=
  CNF.rup_sound cl_32528 [cl_26938,cl_32499] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26938 v h) (hints_cons _ _ _ (der_32499 v h) (by intro d hd; cases hd)))
def cl_32529 : CNF.NClause := [(58,false),(78,true),(27,false),(62,false),(69,false),(85,true)]
theorem der_32529 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32529 :=
  CNF.rup_sound cl_32529 [cl_26939,cl_32477] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26939 v h) (hints_cons _ _ _ (der_32477 v h) (by intro d hd; cases hd)))
def cl_32530 : CNF.NClause := [(58,false),(89,true),(76,true),(62,false),(69,false),(27,true)]
theorem der_32530 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32530 :=
  CNF.rup_sound cl_32530 [cl_26940,cl_32514] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26940 v h) (hints_cons _ _ _ (der_32514 v h) (by intro d hd; cases hd)))
def cl_32531 : CNF.NClause := [(58,false),(69,false),(76,true),(62,true),(27,true),(85,true)]
theorem der_32531 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32531 :=
  CNF.rup_sound cl_32531 [cl_26942,cl_32516] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26942 v h) (hints_cons _ _ _ (der_32516 v h) (by intro d hd; cases hd)))
def cl_32532 : CNF.NClause := [(58,false),(78,true),(76,true),(27,false),(62,false),(85,true)]
theorem der_32532 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32532 :=
  CNF.rup_sound cl_32532 [cl_26943,cl_32481] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26943 v h) (hints_cons _ _ _ (der_32481 v h) (by intro d hd; cases hd)))
def cl_32533 : CNF.NClause := [(58,false),(78,true),(69,true),(27,true),(62,false),(85,true)]
theorem der_32533 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32533 :=
  CNF.rup_sound cl_32533 [cl_26944,cl_32526] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26944 v h) (hints_cons _ _ _ (der_32526 v h) (by intro d hd; cases hd)))
def cl_32535 : CNF.NClause := [(58,false),(85,true),(76,true),(27,true),(62,true),(89,true)]
theorem der_32535 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32535 :=
  CNF.rup_sound cl_32535 [cl_26946,cl_32531] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26946 v h) (hints_cons _ _ _ (der_32531 v h) (by intro d hd; cases hd)))
def cl_32536 : CNF.NClause := [(54,false),(74,false),(89,false),(65,true),(81,false),(83,false)]
theorem der_32536 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32536 :=
  CNF.rup_sound cl_32536 [cl_26950,cl_26947] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26950 v h) (hints_cons _ _ _ (der_26947 v h) (by intro d hd; cases hd)))
def cl_32537 : CNF.NClause := [(54,false),(65,true),(67,false),(89,false),(81,false),(83,false)]
theorem der_32537 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32537 :=
  CNF.rup_sound cl_32537 [cl_26953,cl_26947] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26953 v h) (hints_cons _ _ _ (der_26947 v h) (by intro d hd; cases hd)))
def cl_32538 : CNF.NClause := [(54,false),(83,false),(89,false),(81,false),(23,true),(65,false)]
theorem der_32538 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32538 :=
  CNF.rup_sound cl_32538 [cl_26955,cl_26951] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26955 v h) (hints_cons _ _ _ (der_26951 v h) (by intro d hd; cases hd)))
def cl_32539 : CNF.NClause := [(54,false),(81,false),(65,true),(23,false),(89,false),(83,false)]
theorem der_32539 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32539 :=
  CNF.rup_sound cl_32539 [cl_26956,cl_26952] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26956 v h) (hints_cons _ _ _ (der_26952 v h) (by intro d hd; cases hd)))
def cl_32540 : CNF.NClause := [(54,false),(65,true),(74,true),(89,false),(81,false),(83,false)]
theorem der_32540 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32540 :=
  CNF.rup_sound cl_32540 [cl_26957,cl_32539] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26957 v h) (hints_cons _ _ _ (der_32539 v h) (by intro d hd; cases hd)))
def cl_32541 : CNF.NClause := [(54,false),(83,false),(67,false),(89,false),(74,false),(65,true)]
theorem der_32541 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32541 :=
  CNF.rup_sound cl_32541 [cl_26960,cl_26947] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26960 v h) (hints_cons _ _ _ (der_26947 v h) (by intro d hd; cases hd)))
def cl_32542 : CNF.NClause := [(54,false),(81,true),(89,false),(74,false),(83,false),(65,false)]
theorem der_32542 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32542 :=
  CNF.rup_sound cl_32542 [cl_26962,cl_26958] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26962 v h) (hints_cons _ _ _ (der_26958 v h) (by intro d hd; cases hd)))
def cl_32543 : CNF.NClause := [(54,false),(74,false),(65,true),(23,false),(89,false),(83,false)]
theorem der_32543 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32543 :=
  CNF.rup_sound cl_32543 [cl_26963,cl_32541] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26963 v h) (hints_cons _ _ _ (der_32541 v h) (by intro d hd; cases hd)))
def cl_32544 : CNF.NClause := [(54,false),(74,false),(65,true),(89,false),(83,false),(67,true)]
theorem der_32544 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32544 :=
  CNF.rup_sound cl_32544 [cl_26964,cl_32543] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26964 v h) (hints_cons _ _ _ (der_32543 v h) (by intro d hd; cases hd)))
def cl_32545 : CNF.NClause := [(54,false),(83,false),(74,true),(67,false),(89,false),(65,false)]
theorem der_32545 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32545 :=
  CNF.rup_sound cl_32545 [cl_26966,cl_26965] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26966 v h) (hints_cons _ _ _ (der_26965 v h) (by intro d hd; cases hd)))
def cl_32547 : CNF.NClause := [(54,false),(74,true),(81,true),(67,false),(89,false),(83,false)]
theorem der_32547 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32547 :=
  CNF.rup_sound cl_32547 [cl_26968,cl_32545] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26968 v h) (hints_cons _ _ _ (der_32545 v h) (by intro d hd; cases hd)))
def cl_32548 : CNF.NClause := [(54,false),(74,true),(23,false),(89,false),(83,false),(65,false)]
theorem der_32548 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32548 :=
  CNF.rup_sound cl_32548 [cl_26969,cl_32545] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26969 v h) (hints_cons _ _ _ (der_32545 v h) (by intro d hd; cases hd)))
def cl_32549 : CNF.NClause := [(54,false),(83,false),(81,true),(23,true),(89,false),(65,false)]
theorem der_32549 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32549 :=
  CNF.rup_sound cl_32549 [cl_26970,cl_32542] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26970 v h) (hints_cons _ _ _ (der_32542 v h) (by intro d hd; cases hd)))
def cl_32550 : CNF.NClause := [(54,false),(74,true),(23,false),(65,true),(89,false),(83,false)]
theorem der_32550 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32550 :=
  CNF.rup_sound cl_32550 [cl_26971,cl_32539] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26971 v h) (hints_cons _ _ _ (der_32539 v h) (by intro d hd; cases hd)))
def cl_32551 : CNF.NClause := [(54,false),(74,true),(65,true),(89,false),(83,false),(67,true)]
theorem der_32551 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32551 :=
  CNF.rup_sound cl_32551 [cl_26972,cl_32540] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26972 v h) (hints_cons _ _ _ (der_32540 v h) (by intro d hd; cases hd)))
def cl_32552 : CNF.NClause := [(54,false),(67,false),(89,false),(74,false),(81,false),(65,true)]
theorem der_32552 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32552 :=
  CNF.rup_sound cl_32552 [cl_26975,cl_32537] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26975 v h) (hints_cons _ _ _ (der_32537 v h) (by intro d hd; cases hd)))
def cl_32553 : CNF.NClause := [(54,false),(65,false),(89,false),(74,false),(81,false),(67,true)]
theorem der_32553 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32553 :=
  CNF.rup_sound cl_32553 [cl_26977,cl_26976] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26977 v h) (hints_cons _ _ _ (der_26976 v h) (by intro d hd; cases hd)))
def cl_32555 : CNF.NClause := [(54,false),(74,true),(65,false),(67,false),(89,false),(81,false)]
theorem der_32555 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32555 :=
  CNF.rup_sound cl_32555 [cl_26981,cl_26980] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26981 v h) (hints_cons _ _ _ (der_26980 v h) (by intro d hd; cases hd)))
def cl_32556 : CNF.NClause := [(54,false),(74,true),(23,false),(67,false),(89,false),(81,false)]
theorem der_32556 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32556 :=
  CNF.rup_sound cl_32556 [cl_26982,cl_26980] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26982 v h) (hints_cons _ _ _ (der_26980 v h) (by intro d hd; cases hd)))
def cl_32557 : CNF.NClause := [(54,false),(74,true),(67,false),(89,false),(81,false),(83,true)]
theorem der_32557 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32557 :=
  CNF.rup_sound cl_32557 [cl_26983,cl_32555] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26983 v h) (hints_cons _ _ _ (der_32555 v h) (by intro d hd; cases hd)))
def cl_32558 : CNF.NClause := [(54,false),(74,true),(65,false),(89,false),(81,false),(23,true)]
theorem der_32558 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32558 :=
  CNF.rup_sound cl_32558 [cl_26985,cl_32538] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26985 v h) (hints_cons _ _ _ (der_32538 v h) (by intro d hd; cases hd)))
def cl_32559 : CNF.NClause := [(54,false),(81,false),(65,true),(23,false),(89,false),(67,true)]
theorem der_32559 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32559 :=
  CNF.rup_sound cl_32559 [cl_26986,cl_32539] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26986 v h) (hints_cons _ _ _ (der_32539 v h) (by intro d hd; cases hd)))
def cl_32560 : CNF.NClause := [(54,false),(81,false),(65,true),(89,false),(67,true),(83,true)]
theorem der_32560 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32560 :=
  CNF.rup_sound cl_32560 [cl_26987,cl_32559] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26987 v h) (hints_cons _ _ _ (der_32559 v h) (by intro d hd; cases hd)))
def cl_32561 : CNF.NClause := [(54,false),(65,false),(67,false),(89,false),(74,false),(23,true)]
theorem der_32561 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32561 :=
  CNF.rup_sound cl_32561 [cl_26989,cl_26973] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26989 v h) (hints_cons _ _ _ (der_26973 v h) (by intro d hd; cases hd)))
def cl_32563 : CNF.NClause := [(54,false),(81,true),(67,false),(89,false),(74,false),(65,true)]
theorem der_32563 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32563 :=
  CNF.rup_sound cl_32563 [cl_26991,cl_32541] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26991 v h) (hints_cons _ _ _ (der_32541 v h) (by intro d hd; cases hd)))
def cl_32564 : CNF.NClause := [(54,false),(65,false),(89,false),(74,false),(83,true),(23,false)]
theorem der_32564 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32564 :=
  CNF.rup_sound cl_32564 [cl_26992,cl_26988] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26992 v h) (hints_cons _ _ _ (der_26988 v h) (by intro d hd; cases hd)))
def cl_32565 : CNF.NClause := [(54,false),(81,true),(89,false),(74,false),(67,true),(65,false)]
theorem der_32565 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32565 :=
  CNF.rup_sound cl_32565 [cl_26993,cl_32542] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26993 v h) (hints_cons _ _ _ (der_32542 v h) (by intro d hd; cases hd)))
def cl_32567 : CNF.NClause := [(54,false),(74,false),(65,true),(23,true),(89,false),(67,true)]
theorem der_32567 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32567 :=
  CNF.rup_sound cl_32567 [cl_26995,cl_32544] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26995 v h) (hints_cons _ _ _ (der_32544 v h) (by intro d hd; cases hd)))
def cl_32568 : CNF.NClause := [(54,false),(74,true),(23,false),(67,false),(89,false),(65,false)]
theorem der_32568 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32568 :=
  CNF.rup_sound cl_32568 [cl_26996,cl_26980] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26996 v h) (hints_cons _ _ _ (der_26980 v h) (by intro d hd; cases hd)))
def cl_32569 : CNF.NClause := [(54,false),(74,true),(65,false),(81,true),(67,false),(89,false)]
theorem der_32569 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32569 :=
  CNF.rup_sound cl_32569 [cl_26997,cl_32568] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_26997 v h) (hints_cons _ _ _ (der_32568 v h) (by intro d hd; cases hd)))
def cl_32571 : CNF.NClause := [(54,false),(74,true),(23,false),(89,false),(83,true),(65,false)]
theorem der_32571 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32571 :=
  CNF.rup_sound cl_32571 [cl_27000,cl_32568] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27000 v h) (hints_cons _ _ _ (der_32568 v h) (by intro d hd; cases hd)))
def cl_32572 : CNF.NClause := [(54,false),(74,true),(81,true),(89,false),(83,true),(65,false)]
theorem der_32572 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32572 :=
  CNF.rup_sound cl_32572 [cl_27001,cl_32569] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27001 v h) (hints_cons _ _ _ (der_32569 v h) (by intro d hd; cases hd)))
def cl_32574 : CNF.NClause := [(54,false),(65,true),(23,true),(89,false),(67,true),(83,true)]
theorem der_32574 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32574 :=
  CNF.rup_sound cl_32574 [cl_27003,cl_32567] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27003 v h) (hints_cons _ _ _ (der_32567 v h) (by intro d hd; cases hd)))
def cl_32575 : CNF.NClause := [(54,false),(81,false),(74,false),(23,true),(83,false),(65,false)]
theorem der_32575 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32575 :=
  CNF.rup_sound cl_32575 [cl_27008,cl_27004] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27008 v h) (hints_cons _ _ _ (der_27004 v h) (by intro d hd; cases hd)))
def cl_32576 : CNF.NClause := [(54,false),(74,false),(23,false),(81,false),(83,false),(67,true)]
theorem der_32576 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32576 :=
  CNF.rup_sound cl_32576 [cl_27009,cl_27007] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27009 v h) (hints_cons _ _ _ (der_27007 v h) (by intro d hd; cases hd)))
def cl_32577 : CNF.NClause := [(54,false),(74,false),(23,true),(81,false),(83,false),(67,true)]
theorem der_32577 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32577 :=
  CNF.rup_sound cl_32577 [cl_27010,cl_32575] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27010 v h) (hints_cons _ _ _ (der_32575 v h) (by intro d hd; cases hd)))
def cl_32578 : CNF.NClause := [(54,false),(74,true),(67,false),(81,false),(83,false),(65,false)]
theorem der_32578 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32578 :=
  CNF.rup_sound cl_32578 [cl_27012,cl_32545] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27012 v h) (hints_cons _ _ _ (der_32545 v h) (by intro d hd; cases hd)))
def cl_32579 : CNF.NClause := [(54,false),(74,true),(23,false),(67,false),(81,false),(83,false)]
theorem der_32579 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32579 :=
  CNF.rup_sound cl_32579 [cl_27013,cl_32556] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27013 v h) (hints_cons _ _ _ (der_32556 v h) (by intro d hd; cases hd)))
def cl_32580 : CNF.NClause := [(54,false),(74,true),(67,false),(81,false),(83,false),(89,true)]
theorem der_32580 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32580 :=
  CNF.rup_sound cl_32580 [cl_27014,cl_32578] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27014 v h) (hints_cons _ _ _ (der_32578 v h) (by intro d hd; cases hd)))
def cl_32581 : CNF.NClause := [(54,false),(74,true),(23,false),(81,false),(83,false),(65,false)]
theorem der_32581 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32581 :=
  CNF.rup_sound cl_32581 [cl_27015,cl_26954] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27015 v h) (hints_cons _ _ _ (der_26954 v h) (by intro d hd; cases hd)))
def cl_32582 : CNF.NClause := [(54,false),(67,true),(81,false),(83,false),(23,true),(65,false)]
theorem der_32582 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32582 :=
  CNF.rup_sound cl_32582 [cl_27016,cl_32538] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27016 v h) (hints_cons _ _ _ (der_32538 v h) (by intro d hd; cases hd)))
def cl_32583 : CNF.NClause := [(54,false),(74,true),(23,false),(65,true),(81,false),(83,false)]
theorem der_32583 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32583 :=
  CNF.rup_sound cl_32583 [cl_27017,cl_32539] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27017 v h) (hints_cons _ _ _ (der_32539 v h) (by intro d hd; cases hd)))
def cl_32584 : CNF.NClause := [(54,false),(74,true),(65,true),(81,false),(83,false),(67,true)]
theorem der_32584 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32584 :=
  CNF.rup_sound cl_32584 [cl_27018,cl_32540] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27018 v h) (hints_cons _ _ _ (der_32540 v h) (by intro d hd; cases hd)))
def cl_32585 : CNF.NClause := [(54,false),(65,false),(67,false),(74,false),(83,false),(23,true)]
theorem der_32585 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32585 :=
  CNF.rup_sound cl_32585 [cl_27020,cl_32561] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27020 v h) (hints_cons _ _ _ (der_32561 v h) (by intro d hd; cases hd)))
def cl_32586 : CNF.NClause := [(54,false),(83,false),(65,true),(67,false),(74,false),(23,false)]
theorem der_32586 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32586 :=
  CNF.rup_sound cl_32586 [cl_27021,cl_27005] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27021 v h) (hints_cons _ _ _ (der_27005 v h) (by intro d hd; cases hd)))
def cl_32587 : CNF.NClause := [(54,false),(83,false),(81,true),(67,false),(74,false),(23,true)]
theorem der_32587 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32587 :=
  CNF.rup_sound cl_32587 [cl_27022,cl_32585] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27022 v h) (hints_cons _ _ _ (der_32585 v h) (by intro d hd; cases hd)))
def cl_32588 : CNF.NClause := [(54,false),(65,false),(81,true),(74,false),(83,false),(23,false)]
theorem der_32588 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32588 :=
  CNF.rup_sound cl_32588 [cl_27023,cl_32542] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27023 v h) (hints_cons _ _ _ (der_32542 v h) (by intro d hd; cases hd)))
def cl_32589 : CNF.NClause := [(54,false),(81,true),(74,false),(83,false),(67,true),(65,false)]
theorem der_32589 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32589 :=
  CNF.rup_sound cl_32589 [cl_27024,cl_32542] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27024 v h) (hints_cons _ _ _ (der_32542 v h) (by intro d hd; cases hd)))
def cl_32591 : CNF.NClause := [(54,false),(74,false),(81,true),(83,false),(67,true),(89,true)]
theorem der_32591 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32591 :=
  CNF.rup_sound cl_32591 [cl_27026,cl_32589] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27026 v h) (hints_cons _ _ _ (der_32589 v h) (by intro d hd; cases hd)))
def cl_32592 : CNF.NClause := [(54,false),(74,true),(23,false),(67,false),(83,false),(65,false)]
theorem der_32592 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32592 :=
  CNF.rup_sound cl_32592 [cl_27027,cl_32545] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27027 v h) (hints_cons _ _ _ (der_32545 v h) (by intro d hd; cases hd)))
def cl_32593 : CNF.NClause := [(54,false),(74,true),(65,false),(81,true),(67,false),(83,false)]
theorem der_32593 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32593 :=
  CNF.rup_sound cl_32593 [cl_27028,cl_32592] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27028 v h) (hints_cons _ _ _ (der_32592 v h) (by intro d hd; cases hd)))
def cl_32594 : CNF.NClause := [(54,false),(23,false),(65,true),(81,true),(67,false),(83,false)]
theorem der_32594 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32594 :=
  CNF.rup_sound cl_32594 [cl_27029,cl_32586] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27029 v h) (hints_cons _ _ _ (der_32586 v h) (by intro d hd; cases hd)))
def cl_32595 : CNF.NClause := [(54,false),(74,true),(65,true),(81,true),(67,false),(83,false)]
theorem der_32595 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32595 :=
  CNF.rup_sound cl_32595 [cl_27030,cl_32594] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27030 v h) (hints_cons _ _ _ (der_32594 v h) (by intro d hd; cases hd)))
def cl_32596 : CNF.NClause := [(54,false),(74,true),(23,true),(81,true),(83,false),(65,false)]
theorem der_32596 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32596 :=
  CNF.rup_sound cl_32596 [cl_27032,cl_32549] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27032 v h) (hints_cons _ _ _ (der_32549 v h) (by intro d hd; cases hd)))
def cl_32597 : CNF.NClause := [(54,false),(81,true),(65,true),(23,false),(83,false),(89,true)]
theorem der_32597 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32597 :=
  CNF.rup_sound cl_32597 [cl_27033,cl_32594] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27033 v h) (hints_cons _ _ _ (der_32594 v h) (by intro d hd; cases hd)))
def cl_32598 : CNF.NClause := [(54,false),(81,true),(65,true),(83,false),(67,true),(89,true)]
theorem der_32598 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32598 :=
  CNF.rup_sound cl_32598 [cl_27034,cl_32597] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27034 v h) (hints_cons _ _ _ (der_32597 v h) (by intro d hd; cases hd)))
def cl_32599 : CNF.NClause := [(54,false),(65,false),(67,false),(74,false),(81,false),(89,true)]
theorem der_32599 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32599 :=
  CNF.rup_sound cl_32599 [cl_27036,cl_27035] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27036 v h) (hints_cons _ _ _ (der_27035 v h) (by intro d hd; cases hd)))
def cl_32600 : CNF.NClause := [(54,false),(65,true),(67,false),(74,false),(81,false),(23,false)]
theorem der_32600 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32600 :=
  CNF.rup_sound cl_32600 [cl_27037,cl_27005] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27037 v h) (hints_cons _ _ _ (der_27005 v h) (by intro d hd; cases hd)))
def cl_32601 : CNF.NClause := [(54,false),(65,true),(67,false),(74,false),(81,false),(83,true)]
theorem der_32601 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32601 :=
  CNF.rup_sound cl_32601 [cl_27038,cl_32552] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27038 v h) (hints_cons _ _ _ (der_32552 v h) (by intro d hd; cases hd)))
def cl_32602 : CNF.NClause := [(54,false),(65,false),(74,false),(81,false),(67,true),(23,false)]
theorem der_32602 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32602 :=
  CNF.rup_sound cl_32602 [cl_27039,cl_27007] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27039 v h) (hints_cons _ _ _ (der_27007 v h) (by intro d hd; cases hd)))
def cl_32603 : CNF.NClause := [(54,false),(74,false),(65,false),(81,false),(67,true),(89,true)]
theorem der_32603 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32603 :=
  CNF.rup_sound cl_32603 [cl_27040,cl_32602] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27040 v h) (hints_cons _ _ _ (der_32602 v h) (by intro d hd; cases hd)))
def cl_32604 : CNF.NClause := [(54,false),(74,false),(23,false),(81,false),(67,true),(83,true)]
theorem der_32604 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32604 :=
  CNF.rup_sound cl_32604 [cl_27041,cl_32602] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27041 v h) (hints_cons _ _ _ (der_32602 v h) (by intro d hd; cases hd)))
def cl_32605 : CNF.NClause := [(54,false),(74,false),(65,true),(23,true),(81,false),(67,true)]
theorem der_32605 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32605 :=
  CNF.rup_sound cl_32605 [cl_27042,cl_32577] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27042 v h) (hints_cons _ _ _ (der_32577 v h) (by intro d hd; cases hd)))
def cl_32606 : CNF.NClause := [(54,false),(74,true),(23,false),(67,false),(81,false),(65,false)]
theorem der_32606 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32606 :=
  CNF.rup_sound cl_32606 [cl_27043,cl_26980] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27043 v h) (hints_cons _ _ _ (der_26980 v h) (by intro d hd; cases hd)))
def cl_32607 : CNF.NClause := [(54,false),(74,true),(65,false),(67,false),(81,false),(83,true)]
theorem der_32607 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32607 :=
  CNF.rup_sound cl_32607 [cl_27044,cl_32606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27044 v h) (hints_cons _ _ _ (der_32606 v h) (by intro d hd; cases hd)))
def cl_32608 : CNF.NClause := [(54,false),(74,true),(23,false),(67,false),(81,false),(89,true)]
theorem der_32608 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32608 :=
  CNF.rup_sound cl_32608 [cl_27045,cl_32606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27045 v h) (hints_cons _ _ _ (der_32606 v h) (by intro d hd; cases hd)))
def cl_32609 : CNF.NClause := [(54,false),(74,true),(23,false),(81,false),(83,true),(65,false)]
theorem der_32609 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32609 :=
  CNF.rup_sound cl_32609 [cl_27047,cl_32606] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27047 v h) (hints_cons _ _ _ (der_32606 v h) (by intro d hd; cases hd)))
def cl_32610 : CNF.NClause := [(54,false),(74,true),(65,false),(81,false),(83,true),(89,true)]
theorem der_32610 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32610 :=
  CNF.rup_sound cl_32610 [cl_27048,cl_32609] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27048 v h) (hints_cons _ _ _ (der_32609 v h) (by intro d hd; cases hd)))
def cl_32612 : CNF.NClause := [(54,false),(81,false),(74,true),(23,true),(65,true),(67,true)]
theorem der_32612 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32612 :=
  CNF.rup_sound cl_32612 [cl_27050,cl_32584] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27050 v h) (hints_cons _ _ _ (der_32584 v h) (by intro d hd; cases hd)))
def cl_32613 : CNF.NClause := [(54,false),(65,false),(67,false),(74,false),(83,true),(23,false)]
theorem der_32613 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32613 :=
  CNF.rup_sound cl_32613 [cl_27051,cl_32564] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27051 v h) (hints_cons _ _ _ (der_32564 v h) (by intro d hd; cases hd)))
def cl_32614 : CNF.NClause := [(54,false),(65,false),(67,false),(74,false),(89,true),(23,true)]
theorem der_32614 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32614 :=
  CNF.rup_sound cl_32614 [cl_27052,cl_32599] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27052 v h) (hints_cons _ _ _ (der_32599 v h) (by intro d hd; cases hd)))
def cl_32615 : CNF.NClause := [(54,false),(89,true),(67,false),(74,false),(83,true),(23,false)]
theorem der_32615 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32615 :=
  CNF.rup_sound cl_32615 [cl_27053,cl_32613] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27053 v h) (hints_cons _ _ _ (der_32613 v h) (by intro d hd; cases hd)))
def cl_32616 : CNF.NClause := [(54,false),(65,true),(89,true),(67,false),(74,false),(83,true)]
theorem der_32616 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32616 :=
  CNF.rup_sound cl_32616 [cl_27054,cl_32615] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27054 v h) (hints_cons _ _ _ (der_32615 v h) (by intro d hd; cases hd)))
def cl_32617 : CNF.NClause := [(54,false),(65,false),(74,false),(67,true),(89,true),(23,false)]
theorem der_32617 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32617 :=
  CNF.rup_sound cl_32617 [cl_27055,cl_32602] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27055 v h) (hints_cons _ _ _ (der_32602 v h) (by intro d hd; cases hd)))
def cl_32618 : CNF.NClause := [(54,false),(65,false),(74,false),(67,true),(89,true),(23,true)]
theorem der_32618 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32618 :=
  CNF.rup_sound cl_32618 [cl_27056,cl_32603] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27056 v h) (hints_cons _ _ _ (der_32603 v h) (by intro d hd; cases hd)))
def cl_32619 : CNF.NClause := [(54,false),(81,true),(23,false),(74,false),(67,true),(89,true)]
theorem der_32619 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32619 :=
  CNF.rup_sound cl_32619 [cl_27057,cl_32617] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27057 v h) (hints_cons _ _ _ (der_32617 v h) (by intro d hd; cases hd)))
def cl_32620 : CNF.NClause := [(54,false),(81,true),(65,true),(74,false),(67,true),(89,true)]
theorem der_32620 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32620 :=
  CNF.rup_sound cl_32620 [cl_27058,cl_32619] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27058 v h) (hints_cons _ _ _ (der_32619 v h) (by intro d hd; cases hd)))
def cl_32621 : CNF.NClause := [(54,false),(74,true),(23,false),(81,true),(67,false),(65,false)]
theorem der_32621 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32621 :=
  CNF.rup_sound cl_32621 [cl_27059,cl_32568] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27059 v h) (hints_cons _ _ _ (der_32568 v h) (by intro d hd; cases hd)))
def cl_32622 : CNF.NClause := [(54,false),(65,false),(67,false),(83,true),(89,true),(23,true)]
theorem der_32622 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32622 :=
  CNF.rup_sound cl_32622 [cl_27060,cl_32614] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27060 v h) (hints_cons _ _ _ (der_32614 v h) (by intro d hd; cases hd)))
def cl_32624 : CNF.NClause := [(54,false),(65,true),(89,true),(67,false),(83,true),(23,true)]
theorem der_32624 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32624 :=
  CNF.rup_sound cl_32624 [cl_27062,cl_27046] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27062 v h) (hints_cons _ _ _ (der_27046 v h) (by intro d hd; cases hd)))
def cl_32626 : CNF.NClause := [(54,false),(74,true),(81,true),(67,true),(83,true),(65,false)]
theorem der_32626 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32626 :=
  CNF.rup_sound cl_32626 [cl_27064,cl_32572] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27064 v h) (hints_cons _ _ _ (der_32572 v h) (by intro d hd; cases hd)))
def cl_32628 : CNF.NClause := [(54,false),(74,true),(23,true),(65,true),(67,true),(89,true)]
theorem der_32628 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32628 :=
  CNF.rup_sound cl_32628 [cl_27066,cl_32612] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27066 v h) (hints_cons _ _ _ (der_32612 v h) (by intro d hd; cases hd)))
def cl_32629 : CNF.NClause := [(50,false),(61,false),(46,false),(49,false),(47,true),(108,true)]
theorem der_32629 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32629 :=
  CNF.rup_sound cl_32629 [cl_2947,cl_30052] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2947 v h) (hints_cons _ _ _ (der_30052 v h) (by intro d hd; cases hd)))
def cl_32631 : CNF.NClause := [(45,true),(52,true),(39,true),(46,true),(57,true),(110,false)]
theorem der_32631 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32631 :=
  CNF.rup_sound cl_32631 [cl_3135,cl_23938] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3135 v h) (hints_cons _ _ _ (der_23938 v h) (by intro d hd; cases hd)))
def cl_32632 : CNF.NClause := [(40,false),(55,false),(45,true),(56,true),(50,true),(94,true)]
theorem der_32632 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32632 :=
  CNF.rup_sound cl_32632 [cl_2093,cl_31691] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2093 v h) (hints_cons _ _ _ (der_31691 v h) (by intro d hd; cases hd)))
def cl_32633 : CNF.NClause := [(58,false),(38,false),(45,true),(31,true),(54,true),(120,true)]
theorem der_32633 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32633 :=
  CNF.rup_sound cl_32633 [cl_3734,cl_23703] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3734 v h) (hints_cons _ _ _ (der_23703 v h) (by intro d hd; cases hd)))
def cl_32634 : CNF.NClause := [(54,false),(38,false),(45,true),(31,true),(58,true),(120,true)]
theorem der_32634 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32634 :=
  CNF.rup_sound cl_32634 [cl_3750,cl_23704] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3750 v h) (hints_cons _ _ _ (der_23704 v h) (by intro d hd; cases hd)))
def cl_32636 : CNF.NClause := [(45,true),(31,true),(47,true),(38,true),(58,true),(120,false)]
theorem der_32636 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32636 :=
  CNF.rup_sound cl_32636 [cl_3760,cl_23712] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3760 v h) (hints_cons _ _ _ (der_23712 v h) (by intro d hd; cases hd)))
def cl_32637 : CNF.NClause := [(45,true),(31,true),(38,true),(54,true),(58,true),(120,false)]
theorem der_32637 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32637 :=
  CNF.rup_sound cl_32637 [cl_3768,cl_23712] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3768 v h) (hints_cons _ _ _ (der_23712 v h) (by intro d hd; cases hd)))
def cl_32638 : CNF.NClause := [(31,true),(47,true),(38,true),(54,true),(58,true),(120,false)]
theorem der_32638 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32638 :=
  CNF.rup_sound cl_32638 [cl_3772,cl_23712] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3772 v h) (hints_cons _ _ _ (der_23712 v h) (by intro d hd; cases hd)))
def cl_32639 : CNF.NClause := [(45,true),(31,true),(47,true),(54,true),(58,true),(120,false)]
theorem der_32639 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32639 :=
  CNF.rup_sound cl_32639 [cl_3774,cl_23712] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_3774 v h) (hints_cons _ _ _ (der_23712 v h) (by intro d hd; cases hd)))
def cl_32640 : CNF.NClause := [(40,false),(82,false),(63,true),(88,false),(75,false),(81,false)]
theorem der_32640 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32640 :=
  CNF.rup_sound cl_32640 [cl_27070,cl_27069] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27070 v h) (hints_cons _ _ _ (der_27069 v h) (by intro d hd; cases hd)))
def cl_32641 : CNF.NClause := [(40,false),(69,false),(75,true),(88,false),(82,false),(81,false)]
theorem der_32641 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32641 :=
  CNF.rup_sound cl_32641 [cl_27073,cl_27072] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27073 v h) (hints_cons _ _ _ (der_27072 v h) (by intro d hd; cases hd)))
def cl_32642 : CNF.NClause := [(40,false),(75,true),(63,false),(88,false),(82,false),(81,false)]
theorem der_32642 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32642 :=
  CNF.rup_sound cl_32642 [cl_27074,cl_32417] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27074 v h) (hints_cons _ _ _ (der_32417 v h) (by intro d hd; cases hd)))
def cl_32643 : CNF.NClause := [(40,false),(75,true),(9,false),(88,false),(82,false),(81,false)]
theorem der_32643 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32643 :=
  CNF.rup_sound cl_32643 [cl_27075,cl_32642] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27075 v h) (hints_cons _ _ _ (der_32642 v h) (by intro d hd; cases hd)))
def cl_32644 : CNF.NClause := [(40,false),(88,false),(75,true),(9,true),(82,false),(81,false)]
theorem der_32644 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32644 :=
  CNF.rup_sound cl_32644 [cl_27076,cl_32417] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27076 v h) (hints_cons _ _ _ (der_32417 v h) (by intro d hd; cases hd)))
def cl_32645 : CNF.NClause := [(40,false),(75,false),(81,true),(88,false),(82,false),(69,false)]
theorem der_32645 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32645 :=
  CNF.rup_sound cl_32645 [cl_27079,cl_27078] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27079 v h) (hints_cons _ _ _ (der_27078 v h) (by intro d hd; cases hd)))
def cl_32646 : CNF.NClause := [(40,false),(75,false),(81,true),(63,false),(88,false),(82,false)]
theorem der_32646 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32646 :=
  CNF.rup_sound cl_32646 [cl_27080,cl_32422] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27080 v h) (hints_cons _ _ _ (der_32422 v h) (by intro d hd; cases hd)))
def cl_32647 : CNF.NClause := [(40,false),(9,false),(63,true),(88,false),(82,false),(75,false)]
theorem der_32647 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32647 :=
  CNF.rup_sound cl_32647 [cl_27081,cl_27069] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27081 v h) (hints_cons _ _ _ (der_27069 v h) (by intro d hd; cases hd)))
def cl_32649 : CNF.NClause := [(40,false),(75,true),(63,false),(88,false),(82,false),(69,false)]
theorem der_32649 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32649 :=
  CNF.rup_sound cl_32649 [cl_27083,cl_32420] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27083 v h) (hints_cons _ _ _ (der_32420 v h) (by intro d hd; cases hd)))
def cl_32650 : CNF.NClause := [(40,false),(75,true),(9,false),(88,false),(82,false),(69,false)]
theorem der_32650 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32650 :=
  CNF.rup_sound cl_32650 [cl_27084,cl_32649] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27084 v h) (hints_cons _ _ _ (der_32649 v h) (by intro d hd; cases hd)))
def cl_32651 : CNF.NClause := [(40,false),(69,false),(75,true),(88,false),(9,true),(82,false)]
theorem der_32651 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32651 :=
  CNF.rup_sound cl_32651 [cl_27085,cl_32419] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27085 v h) (hints_cons _ _ _ (der_32419 v h) (by intro d hd; cases hd)))
def cl_32653 : CNF.NClause := [(40,false),(69,true),(75,true),(9,false),(88,false),(82,false)]
theorem der_32653 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32653 :=
  CNF.rup_sound cl_32653 [cl_27087,cl_32643] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27087 v h) (hints_cons _ _ _ (der_32643 v h) (by intro d hd; cases hd)))
def cl_32654 : CNF.NClause := [(40,false),(88,false),(9,true),(63,false),(69,false),(75,false)]
theorem der_32654 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32654 :=
  CNF.rup_sound cl_32654 [cl_27089,cl_32418] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27089 v h) (hints_cons _ _ _ (der_32418 v h) (by intro d hd; cases hd)))
def cl_32655 : CNF.NClause := [(40,false),(75,false),(88,false),(69,false),(81,false),(82,true)]
theorem der_32655 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32655 :=
  CNF.rup_sound cl_32655 [cl_27091,cl_27090] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27091 v h) (hints_cons _ _ _ (der_27090 v h) (by intro d hd; cases hd)))
def cl_32656 : CNF.NClause := [(40,false),(69,true),(63,false),(88,false),(75,false),(81,false)]
theorem der_32656 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32656 :=
  CNF.rup_sound cl_32656 [cl_27092,cl_27068] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27092 v h) (hints_cons _ _ _ (der_27068 v h) (by intro d hd; cases hd)))
def cl_32657 : CNF.NClause := [(40,false),(9,false),(88,false),(75,false),(81,false),(82,true)]
theorem der_32657 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32657 :=
  CNF.rup_sound cl_32657 [cl_27093,cl_27090] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27093 v h) (hints_cons _ _ _ (der_27090 v h) (by intro d hd; cases hd)))
def cl_32658 : CNF.NClause := [(40,false),(69,true),(88,false),(75,false),(81,false),(82,true)]
theorem der_32658 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32658 :=
  CNF.rup_sound cl_32658 [cl_27094,cl_32656] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27094 v h) (hints_cons _ _ _ (der_32656 v h) (by intro d hd; cases hd)))
def cl_32659 : CNF.NClause := [(40,false),(75,true),(63,false),(88,false),(69,false),(81,false)]
theorem der_32659 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32659 :=
  CNF.rup_sound cl_32659 [cl_27095,cl_32430] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27095 v h) (hints_cons _ _ _ (der_32430 v h) (by intro d hd; cases hd)))
def cl_32660 : CNF.NClause := [(40,false),(75,true),(9,false),(88,false),(69,false),(81,false)]
theorem der_32660 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32660 :=
  CNF.rup_sound cl_32660 [cl_27096,cl_32659] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27096 v h) (hints_cons _ _ _ (der_32659 v h) (by intro d hd; cases hd)))
def cl_32661 : CNF.NClause := [(40,false),(81,false),(75,true),(63,true),(88,false),(69,false)]
theorem der_32661 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32661 :=
  CNF.rup_sound cl_32661 [cl_27097,cl_32660] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27097 v h) (hints_cons _ _ _ (der_32660 v h) (by intro d hd; cases hd)))
def cl_32662 : CNF.NClause := [(40,false),(69,true),(75,true),(63,false),(88,false),(81,false)]
theorem der_32662 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32662 :=
  CNF.rup_sound cl_32662 [cl_27098,cl_32642] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27098 v h) (hints_cons _ _ _ (der_32642 v h) (by intro d hd; cases hd)))
def cl_32663 : CNF.NClause := [(40,false),(69,true),(75,true),(88,false),(81,false),(82,true)]
theorem der_32663 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32663 :=
  CNF.rup_sound cl_32663 [cl_27100,cl_32662] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27100 v h) (hints_cons _ _ _ (der_32662 v h) (by intro d hd; cases hd)))
def cl_32664 : CNF.NClause := [(40,false),(75,false),(81,true),(63,false),(88,false),(69,false)]
theorem der_32664 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32664 :=
  CNF.rup_sound cl_32664 [cl_27101,cl_32422] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27101 v h) (hints_cons _ _ _ (der_32422 v h) (by intro d hd; cases hd)))
def cl_32665 : CNF.NClause := [(40,false),(75,false),(9,false),(81,true),(88,false),(69,false)]
theorem der_32665 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32665 :=
  CNF.rup_sound cl_32665 [cl_27102,cl_32664] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27102 v h) (hints_cons _ _ _ (der_32664 v h) (by intro d hd; cases hd)))
def cl_32666 : CNF.NClause := [(40,false),(63,true),(81,true),(88,false),(69,false),(75,false)]
theorem der_32666 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32666 :=
  CNF.rup_sound cl_32666 [cl_27103,cl_32645] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27103 v h) (hints_cons _ _ _ (der_32645 v h) (by intro d hd; cases hd)))
def cl_32667 : CNF.NClause := [(40,false),(9,false),(81,true),(63,false),(88,false),(75,false)]
theorem der_32667 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32667 :=
  CNF.rup_sound cl_32667 [cl_27104,cl_32665] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27104 v h) (hints_cons _ _ _ (der_32665 v h) (by intro d hd; cases hd)))
def cl_32668 : CNF.NClause := [(40,false),(69,true),(63,true),(9,false),(88,false),(75,false)]
theorem der_32668 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32668 :=
  CNF.rup_sound cl_32668 [cl_27105,cl_32647] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27105 v h) (hints_cons _ _ _ (der_32647 v h) (by intro d hd; cases hd)))
def cl_32669 : CNF.NClause := [(40,false),(81,true),(9,true),(63,true),(88,false),(75,false)]
theorem der_32669 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32669 :=
  CNF.rup_sound cl_32669 [cl_27106,cl_32666] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27106 v h) (hints_cons _ _ _ (der_32666 v h) (by intro d hd; cases hd)))
def cl_32670 : CNF.NClause := [(40,false),(75,true),(9,false),(63,false),(88,false),(69,false)]
theorem der_32670 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32670 :=
  CNF.rup_sound cl_32670 [cl_27107,cl_32660] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27107 v h) (hints_cons _ _ _ (der_32660 v h) (by intro d hd; cases hd)))
def cl_32671 : CNF.NClause := [(40,false),(75,true),(63,true),(88,false),(69,false),(82,true)]
theorem der_32671 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32671 :=
  CNF.rup_sound cl_32671 [cl_27109,cl_32661] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27109 v h) (hints_cons _ _ _ (der_32661 v h) (by intro d hd; cases hd)))
def cl_32672 : CNF.NClause := [(40,false),(69,true),(75,true),(63,false),(88,false),(82,true)]
theorem der_32672 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32672 :=
  CNF.rup_sound cl_32672 [cl_27110,cl_32663] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27110 v h) (hints_cons _ _ _ (der_32663 v h) (by intro d hd; cases hd)))
def cl_32673 : CNF.NClause := [(40,false),(69,true),(75,true),(9,false),(88,false),(82,true)]
theorem der_32673 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32673 :=
  CNF.rup_sound cl_32673 [cl_27111,cl_32672] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27111 v h) (hints_cons _ _ _ (der_32672 v h) (by intro d hd; cases hd)))
def cl_32674 : CNF.NClause := [(40,false),(75,true),(69,true),(9,true),(88,false),(82,true)]
theorem der_32674 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32674 :=
  CNF.rup_sound cl_32674 [cl_27112,cl_32663] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27112 v h) (hints_cons _ _ _ (der_32663 v h) (by intro d hd; cases hd)))
def cl_32675 : CNF.NClause := [(40,false),(81,false),(63,false),(82,false),(69,false),(9,true)]
theorem der_32675 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32675 :=
  CNF.rup_sound cl_32675 [cl_27113,cl_26782] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27113 v h) (hints_cons _ _ _ (der_26782 v h) (by intro d hd; cases hd)))
def cl_32676 : CNF.NClause := [(40,false),(69,false),(82,false),(75,false),(81,false),(88,true)]
theorem der_32676 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32676 :=
  CNF.rup_sound cl_32676 [cl_27115,cl_27114] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27115 v h) (hints_cons _ _ _ (der_27114 v h) (by intro d hd; cases hd)))
def cl_32677 : CNF.NClause := [(40,false),(69,true),(63,false),(82,false),(75,false),(81,false)]
theorem der_32677 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32677 :=
  CNF.rup_sound cl_32677 [cl_27116,cl_26795] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27116 v h) (hints_cons _ _ _ (der_26795 v h) (by intro d hd; cases hd)))
def cl_32678 : CNF.NClause := [(40,false),(69,true),(9,false),(82,false),(75,false),(81,false)]
theorem der_32678 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32678 :=
  CNF.rup_sound cl_32678 [cl_27117,cl_32677] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27117 v h) (hints_cons _ _ _ (der_32677 v h) (by intro d hd; cases hd)))
def cl_32679 : CNF.NClause := [(40,false),(69,true),(63,true),(82,false),(75,false),(81,false)]
theorem der_32679 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32679 :=
  CNF.rup_sound cl_32679 [cl_27118,cl_32640] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27118 v h) (hints_cons _ _ _ (der_32640 v h) (by intro d hd; cases hd)))
def cl_32680 : CNF.NClause := [(40,false),(75,true),(63,false),(82,false),(69,false),(81,false)]
theorem der_32680 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32680 :=
  CNF.rup_sound cl_32680 [cl_27119,cl_27071] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27119 v h) (hints_cons _ _ _ (der_27071 v h) (by intro d hd; cases hd)))
def cl_32681 : CNF.NClause := [(40,false),(69,false),(75,true),(9,true),(82,false),(81,false)]
theorem der_32681 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32681 :=
  CNF.rup_sound cl_32681 [cl_27121,cl_32644] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27121 v h) (hints_cons _ _ _ (der_32644 v h) (by intro d hd; cases hd)))
def cl_32682 : CNF.NClause := [(40,false),(69,true),(75,true),(63,false),(82,false),(81,false)]
theorem der_32682 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32682 :=
  CNF.rup_sound cl_32682 [cl_27122,cl_32642] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27122 v h) (hints_cons _ _ _ (der_32642 v h) (by intro d hd; cases hd)))
def cl_32683 : CNF.NClause := [(40,false),(63,true),(9,false),(82,false),(81,false),(88,true)]
theorem der_32683 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32683 :=
  CNF.rup_sound cl_32683 [cl_27123,cl_27120] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27123 v h) (hints_cons _ _ _ (der_27120 v h) (by intro d hd; cases hd)))
def cl_32684 : CNF.NClause := [(40,false),(69,true),(63,true),(82,false),(81,false),(88,true)]
theorem der_32684 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32684 :=
  CNF.rup_sound cl_32684 [cl_27124,cl_32679] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27124 v h) (hints_cons _ _ _ (der_32679 v h) (by intro d hd; cases hd)))
def cl_32685 : CNF.NClause := [(40,false),(81,true),(63,false),(82,false),(69,false),(75,false)]
theorem der_32685 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32685 :=
  CNF.rup_sound cl_32685 [cl_27125,cl_27077] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27125 v h) (hints_cons _ _ _ (der_27077 v h) (by intro d hd; cases hd)))
def cl_32686 : CNF.NClause := [(40,false),(81,true),(9,false),(82,false),(69,false),(75,false)]
theorem der_32686 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32686 :=
  CNF.rup_sound cl_32686 [cl_27126,cl_32685] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27126 v h) (hints_cons _ _ _ (der_32685 v h) (by intro d hd; cases hd)))
def cl_32687 : CNF.NClause := [(40,false),(81,true),(82,false),(69,false),(75,false),(88,true)]
theorem der_32687 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32687 :=
  CNF.rup_sound cl_32687 [cl_27127,cl_32686] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27127 v h) (hints_cons _ _ _ (der_32686 v h) (by intro d hd; cases hd)))
def cl_32688 : CNF.NClause := [(40,false),(9,false),(81,true),(63,false),(82,false),(75,false)]
theorem der_32688 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32688 :=
  CNF.rup_sound cl_32688 [cl_27128,cl_32686] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27128 v h) (hints_cons _ _ _ (der_32686 v h) (by intro d hd; cases hd)))
def cl_32689 : CNF.NClause := [(40,false),(69,true),(63,true),(9,false),(82,false),(75,false)]
theorem der_32689 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32689 :=
  CNF.rup_sound cl_32689 [cl_27129,cl_32647] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27129 v h) (hints_cons _ _ _ (der_32647 v h) (by intro d hd; cases hd)))
def cl_32690 : CNF.NClause := [(40,false),(81,true),(63,true),(9,true),(82,false),(75,false)]
theorem der_32690 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32690 :=
  CNF.rup_sound cl_32690 [cl_27130,cl_32669] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27130 v h) (hints_cons _ _ _ (der_32669 v h) (by intro d hd; cases hd)))
def cl_32691 : CNF.NClause := [(40,false),(9,false),(81,true),(63,false),(82,false),(69,false)]
theorem der_32691 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32691 :=
  CNF.rup_sound cl_32691 [cl_27131,cl_32686] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27131 v h) (hints_cons _ _ _ (der_32686 v h) (by intro d hd; cases hd)))
def cl_32692 : CNF.NClause := [(40,false),(9,false),(81,true),(82,false),(69,false),(88,true)]
theorem der_32692 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32692 :=
  CNF.rup_sound cl_32692 [cl_27132,cl_32686] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27132 v h) (hints_cons _ _ _ (der_32686 v h) (by intro d hd; cases hd)))
def cl_32693 : CNF.NClause := [(40,false),(69,false),(81,true),(82,false),(9,true),(88,true)]
theorem der_32693 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32693 :=
  CNF.rup_sound cl_32693 [cl_27133,cl_32427] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27133 v h) (hints_cons _ _ _ (der_32427 v h) (by intro d hd; cases hd)))
def cl_32694 : CNF.NClause := [(40,false),(69,true),(9,false),(81,true),(63,false),(82,false)]
theorem der_32694 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32694 :=
  CNF.rup_sound cl_32694 [cl_27134,cl_32688] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27134 v h) (hints_cons _ _ _ (der_32688 v h) (by intro d hd; cases hd)))
def cl_32695 : CNF.NClause := [(40,false),(69,true),(63,true),(9,false),(81,true),(82,false)]
theorem der_32695 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32695 :=
  CNF.rup_sound cl_32695 [cl_27135,cl_32689] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27135 v h) (hints_cons _ _ _ (der_32689 v h) (by intro d hd; cases hd)))
def cl_32696 : CNF.NClause := [(40,false),(69,true),(75,true),(63,true),(81,true),(82,false)]
theorem der_32696 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32696 :=
  CNF.rup_sound cl_32696 [cl_27136,cl_27088] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27136 v h) (hints_cons _ _ _ (der_27088 v h) (by intro d hd; cases hd)))
def cl_32697 : CNF.NClause := [(40,false),(88,true),(69,false),(75,false),(81,false),(63,false)]
theorem der_32697 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32697 :=
  CNF.rup_sound cl_32697 [cl_27138,cl_32676] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27138 v h) (hints_cons _ _ _ (der_32676 v h) (by intro d hd; cases hd)))
def cl_32698 : CNF.NClause := [(40,false),(69,false),(88,true),(75,false),(81,false),(9,false)]
theorem der_32698 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32698 :=
  CNF.rup_sound cl_32698 [cl_27139,cl_27114] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27139 v h) (hints_cons _ _ _ (der_27114 v h) (by intro d hd; cases hd)))
def cl_32699 : CNF.NClause := [(40,false),(69,false),(9,true),(75,false),(81,false),(88,true)]
theorem der_32699 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32699 :=
  CNF.rup_sound cl_32699 [cl_27140,cl_32697] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27140 v h) (hints_cons _ _ _ (der_32697 v h) (by intro d hd; cases hd)))
def cl_32700 : CNF.NClause := [(40,false),(69,true),(9,false),(63,false),(75,false),(81,false)]
theorem der_32700 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32700 :=
  CNF.rup_sound cl_32700 [cl_27141,cl_32678] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27141 v h) (hints_cons _ _ _ (der_32678 v h) (by intro d hd; cases hd)))
def cl_32701 : CNF.NClause := [(40,false),(69,true),(63,true),(9,false),(75,false),(81,false)]
theorem der_32701 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32701 :=
  CNF.rup_sound cl_32701 [cl_27142,cl_32679] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27142 v h) (hints_cons _ _ _ (der_32679 v h) (by intro d hd; cases hd)))
def cl_32702 : CNF.NClause := [(40,false),(75,false),(69,true),(63,true),(81,false),(82,true)]
theorem der_32702 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32702 :=
  CNF.rup_sound cl_32702 [cl_27143,cl_32701] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27143 v h) (hints_cons _ _ _ (der_32701 v h) (by intro d hd; cases hd)))
def cl_32703 : CNF.NClause := [(40,false),(88,true),(9,false),(69,false),(81,false),(63,true)]
theorem der_32703 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32703 :=
  CNF.rup_sound cl_32703 [cl_27145,cl_27120] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27145 v h) (hints_cons _ _ _ (der_27120 v h) (by intro d hd; cases hd)))
def cl_32704 : CNF.NClause := [(40,false),(75,true),(63,true),(69,false),(81,false),(82,true)]
theorem der_32704 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32704 :=
  CNF.rup_sound cl_32704 [cl_27146,cl_32661] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27146 v h) (hints_cons _ _ _ (der_32661 v h) (by intro d hd; cases hd)))
def cl_32705 : CNF.NClause := [(40,false),(9,false),(63,false),(81,false),(82,true),(88,true)]
theorem der_32705 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32705 :=
  CNF.rup_sound cl_32705 [cl_27147,cl_27144] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27147 v h) (hints_cons _ _ _ (der_27144 v h) (by intro d hd; cases hd)))
def cl_32706 : CNF.NClause := [(40,false),(69,true),(63,true),(9,false),(81,false),(82,true)]
theorem der_32706 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32706 :=
  CNF.rup_sound cl_32706 [cl_27148,cl_32701] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27148 v h) (hints_cons _ _ _ (der_32701 v h) (by intro d hd; cases hd)))
def cl_32707 : CNF.NClause := [(40,false),(81,false),(69,true),(63,true),(82,true),(88,true)]
theorem der_32707 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32707 :=
  CNF.rup_sound cl_32707 [cl_27149,cl_32706] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27149 v h) (hints_cons _ _ _ (der_32706 v h) (by intro d hd; cases hd)))
def cl_32709 : CNF.NClause := [(40,false),(88,true),(81,true),(69,false),(75,false),(9,true)]
theorem der_32709 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32709 :=
  CNF.rup_sound cl_32709 [cl_27152,cl_32433] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27152 v h) (hints_cons _ _ _ (der_32433 v h) (by intro d hd; cases hd)))
def cl_32710 : CNF.NClause := [(40,false),(69,true),(9,false),(81,true),(63,false),(75,false)]
theorem der_32710 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32710 :=
  CNF.rup_sound cl_32710 [cl_27153,cl_32667] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27153 v h) (hints_cons _ _ _ (der_32667 v h) (by intro d hd; cases hd)))
def cl_32711 : CNF.NClause := [(40,false),(81,true),(69,true),(9,true),(63,true),(75,false)]
theorem der_32711 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32711 :=
  CNF.rup_sound cl_32711 [cl_27155,cl_32690] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27155 v h) (hints_cons _ _ _ (der_32690 v h) (by intro d hd; cases hd)))
def cl_32713 : CNF.NClause := [(40,false),(88,true),(75,true),(81,true),(69,false),(9,true)]
theorem der_32713 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32713 :=
  CNF.rup_sound cl_32713 [cl_27158,cl_32693] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27158 v h) (hints_cons _ _ _ (der_32693 v h) (by intro d hd; cases hd)))
def cl_32714 : CNF.NClause := [(40,false),(69,true),(75,true),(81,true),(63,false),(82,true)]
theorem der_32714 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32714 :=
  CNF.rup_sound cl_32714 [cl_27159,cl_32672] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27159 v h) (hints_cons _ _ _ (der_32672 v h) (by intro d hd; cases hd)))
def cl_32715 : CNF.NClause := [(40,false),(69,true),(9,true),(63,true),(82,true),(88,true)]
theorem der_32715 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32715 :=
  CNF.rup_sound cl_32715 [cl_27161,cl_32707] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27161 v h) (hints_cons _ _ _ (der_32707 v h) (by intro d hd; cases hd)))
def cl_32717 : CNF.NClause := [(50,false),(40,false),(45,false),(55,false),(56,true),(94,true)]
theorem der_32717 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32717 :=
  CNF.rup_sound cl_32717 [cl_2081,cl_25926] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (inp_2081 v h) (hints_cons _ _ _ (der_25926 v h) (by intro d hd; cases hd)))
def cl_32719 : CNF.NClause := [(60,false),(62,true),(88,false),(86,false),(80,false),(68,false)]
theorem der_32719 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32719 :=
  CNF.rup_sound cl_32719 [cl_27168,cl_27162] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27168 v h) (hints_cons _ _ _ (der_27162 v h) (by intro d hd; cases hd)))
def cl_32721 : CNF.NClause := [(60,false),(62,true),(29,false),(88,false),(86,false),(80,false)]
theorem der_32721 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32721 :=
  CNF.rup_sound cl_32721 [cl_27171,cl_27164] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27171 v h) (hints_cons _ _ _ (der_27164 v h) (by intro d hd; cases hd)))
def cl_32722 : CNF.NClause := [(60,false),(74,true),(62,true),(88,false),(86,false),(80,false)]
theorem der_32722 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32722 :=
  CNF.rup_sound cl_32722 [cl_27172,cl_32719] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27172 v h) (hints_cons _ _ _ (der_32719 v h) (by intro d hd; cases hd)))
def cl_32723 : CNF.NClause := [(60,false),(74,false),(62,true),(88,false),(86,false),(68,false)]
theorem der_32723 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32723 :=
  CNF.rup_sound cl_32723 [cl_27175,cl_27174] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27175 v h) (hints_cons _ _ _ (der_27174 v h) (by intro d hd; cases hd)))
def cl_32724 : CNF.NClause := [(60,false),(86,false),(62,true),(88,false),(29,true),(74,false)]
theorem der_32724 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32724 :=
  CNF.rup_sound cl_32724 [cl_27179,cl_32723] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27179 v h) (hints_cons _ _ _ (der_32723 v h) (by intro d hd; cases hd)))
def cl_32725 : CNF.NClause := [(60,false),(74,true),(88,false),(62,false),(86,false),(68,false)]
theorem der_32725 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32725 :=
  CNF.rup_sound cl_32725 [cl_27181,cl_27166] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27181 v h) (hints_cons _ _ _ (der_27166 v h) (by intro d hd; cases hd)))
def cl_32727 : CNF.NClause := [(60,false),(74,true),(80,true),(88,false),(86,false),(68,false)]
theorem der_32727 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32727 :=
  CNF.rup_sound cl_32727 [cl_27183,cl_32725] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27183 v h) (hints_cons _ _ _ (der_32725 v h) (by intro d hd; cases hd)))
def cl_32728 : CNF.NClause := [(60,false),(62,false),(74,true),(29,true),(88,false),(86,false)]
theorem der_32728 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32728 :=
  CNF.rup_sound cl_32728 [cl_27185,cl_32725] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27185 v h) (hints_cons _ _ _ (der_32725 v h) (by intro d hd; cases hd)))
def cl_32730 : CNF.NClause := [(60,false),(74,true),(68,true),(62,true),(88,false),(86,false)]
theorem der_32730 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32730 :=
  CNF.rup_sound cl_32730 [cl_27187,cl_32722] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27187 v h) (hints_cons _ _ _ (der_32722 v h) (by intro d hd; cases hd)))
def cl_32731 : CNF.NClause := [(60,false),(74,false),(29,true),(88,false),(80,false),(68,false)]
theorem der_32731 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32731 :=
  CNF.rup_sound cl_32731 [cl_27190,cl_27188] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27190 v h) (hints_cons _ _ _ (der_27188 v h) (by intro d hd; cases hd)))
def cl_32732 : CNF.NClause := [(60,false),(74,false),(88,false),(62,false),(29,true),(80,false)]
theorem der_32732 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32732 :=
  CNF.rup_sound cl_32732 [cl_27192,cl_27163] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27192 v h) (hints_cons _ _ _ (der_27163 v h) (by intro d hd; cases hd)))
def cl_32733 : CNF.NClause := [(60,false),(62,true),(29,false),(88,false),(74,false),(80,false)]
theorem der_32733 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32733 :=
  CNF.rup_sound cl_32733 [cl_27193,cl_27189] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27193 v h) (hints_cons _ _ _ (der_27189 v h) (by intro d hd; cases hd)))
def cl_32734 : CNF.NClause := [(60,false),(74,true),(29,false),(88,false),(80,false),(68,false)]
theorem der_32734 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32734 :=
  CNF.rup_sound cl_32734 [cl_27197,cl_27195] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27197 v h) (hints_cons _ _ _ (der_27195 v h) (by intro d hd; cases hd)))
def cl_32735 : CNF.NClause := [(60,false),(74,true),(62,true),(88,false),(80,false),(68,false)]
theorem der_32735 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32735 :=
  CNF.rup_sound cl_32735 [cl_27198,cl_32719] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27198 v h) (hints_cons _ _ _ (der_32719 v h) (by intro d hd; cases hd)))
def cl_32736 : CNF.NClause := [(60,false),(74,true),(29,false),(88,false),(62,false),(80,false)]
theorem der_32736 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32736 :=
  CNF.rup_sound cl_32736 [cl_27199,cl_27195] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27199 v h) (hints_cons _ _ _ (der_27195 v h) (by intro d hd; cases hd)))
def cl_32737 : CNF.NClause := [(60,false),(62,false),(74,true),(68,true),(88,false),(80,false)]
theorem der_32737 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32737 :=
  CNF.rup_sound cl_32737 [cl_27200,cl_32736] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27200 v h) (hints_cons _ _ _ (der_32736 v h) (by intro d hd; cases hd)))
def cl_32738 : CNF.NClause := [(60,false),(68,true),(62,true),(29,false),(88,false),(80,false)]
theorem der_32738 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32738 :=
  CNF.rup_sound cl_32738 [cl_27201,cl_32721] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27201 v h) (hints_cons _ _ _ (der_32721 v h) (by intro d hd; cases hd)))
def cl_32740 : CNF.NClause := [(60,false),(62,true),(29,false),(88,false),(74,false),(68,false)]
theorem der_32740 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32740 :=
  CNF.rup_sound cl_32740 [cl_27205,cl_27189] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27205 v h) (hints_cons _ _ _ (der_27189 v h) (by intro d hd; cases hd)))
def cl_32741 : CNF.NClause := [(60,false),(74,false),(86,true),(88,false),(29,true),(68,false)]
theorem der_32741 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32741 :=
  CNF.rup_sound cl_32741 [cl_27206,cl_32731] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27206 v h) (hints_cons _ _ _ (der_32731 v h) (by intro d hd; cases hd)))
def cl_32742 : CNF.NClause := [(60,false),(68,true),(29,false),(88,false),(62,false),(74,false)]
theorem der_32742 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32742 :=
  CNF.rup_sound cl_32742 [cl_27207,cl_27191] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27207 v h) (hints_cons _ _ _ (der_27191 v h) (by intro d hd; cases hd)))
def cl_32743 : CNF.NClause := [(60,false),(74,false),(68,true),(86,true),(88,false),(62,false)]
theorem der_32743 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32743 :=
  CNF.rup_sound cl_32743 [cl_27208,cl_32742] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27208 v h) (hints_cons _ _ _ (der_32742 v h) (by intro d hd; cases hd)))
def cl_32744 : CNF.NClause := [(60,false),(68,true),(86,true),(29,false),(88,false),(74,false)]
theorem der_32744 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32744 :=
  CNF.rup_sound cl_32744 [cl_27209,cl_32742] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27209 v h) (hints_cons _ _ _ (der_32742 v h) (by intro d hd; cases hd)))
def cl_32745 : CNF.NClause := [(60,false),(68,true),(86,true),(80,true),(88,false),(74,false)]
theorem der_32745 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32745 :=
  CNF.rup_sound cl_32745 [cl_27210,cl_32743] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27210 v h) (hints_cons _ _ _ (der_32743 v h) (by intro d hd; cases hd)))
def cl_32746 : CNF.NClause := [(60,false),(74,true),(29,false),(88,false),(62,false),(68,false)]
theorem der_32746 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32746 :=
  CNF.rup_sound cl_32746 [cl_27211,cl_32734] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27211 v h) (hints_cons _ _ _ (der_32734 v h) (by intro d hd; cases hd)))
def cl_32748 : CNF.NClause := [(60,false),(74,true),(62,true),(29,false),(88,false),(68,false)]
theorem der_32748 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32748 :=
  CNF.rup_sound cl_32748 [cl_27213,cl_32734] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27213 v h) (hints_cons _ _ _ (der_32734 v h) (by intro d hd; cases hd)))
def cl_32749 : CNF.NClause := [(60,false),(88,false),(74,true),(62,true),(86,true),(68,false)]
theorem der_32749 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32749 :=
  CNF.rup_sound cl_32749 [cl_27214,cl_32748] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27214 v h) (hints_cons _ _ _ (der_32748 v h) (by intro d hd; cases hd)))
def cl_32750 : CNF.NClause := [(60,false),(74,true),(86,true),(29,false),(88,false),(62,false)]
theorem der_32750 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32750 :=
  CNF.rup_sound cl_32750 [cl_27215,cl_32736] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27215 v h) (hints_cons _ _ _ (der_32736 v h) (by intro d hd; cases hd)))
def cl_32751 : CNF.NClause := [(60,false),(88,false),(74,true),(68,true),(86,true),(62,false)]
theorem der_32751 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32751 :=
  CNF.rup_sound cl_32751 [cl_27216,cl_32750] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27216 v h) (hints_cons _ _ _ (der_32750 v h) (by intro d hd; cases hd)))
def cl_32752 : CNF.NClause := [(60,false),(68,true),(62,true),(86,true),(29,false),(88,false)]
theorem der_32752 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32752 :=
  CNF.rup_sound cl_32752 [cl_27217,cl_32738] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27217 v h) (hints_cons _ _ _ (der_32738 v h) (by intro d hd; cases hd)))
def cl_32753 : CNF.NClause := [(60,false),(62,true),(74,true),(68,true),(29,true),(88,false)]
theorem der_32753 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32753 :=
  CNF.rup_sound cl_32753 [cl_27218,cl_32730] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27218 v h) (hints_cons _ _ _ (der_32730 v h) (by intro d hd; cases hd)))
def cl_32754 : CNF.NClause := [(60,false),(86,false),(29,true),(74,false),(80,false),(68,false)]
theorem der_32754 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32754 :=
  CNF.rup_sound cl_32754 [cl_27221,cl_27219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27221 v h) (hints_cons _ _ _ (der_27219 v h) (by intro d hd; cases hd)))
def cl_32755 : CNF.NClause := [(60,false),(86,false),(62,false),(29,true),(74,false),(80,false)]
theorem der_32755 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32755 :=
  CNF.rup_sound cl_32755 [cl_27223,cl_27219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27223 v h) (hints_cons _ _ _ (der_27219 v h) (by intro d hd; cases hd)))
def cl_32756 : CNF.NClause := [(60,false),(62,true),(29,false),(86,false),(74,false),(80,false)]
theorem der_32756 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32756 :=
  CNF.rup_sound cl_32756 [cl_27224,cl_27220] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27224 v h) (hints_cons _ _ _ (der_27220 v h) (by intro d hd; cases hd)))
def cl_32757 : CNF.NClause := [(60,false),(74,true),(62,false),(86,false),(80,false),(68,false)]
theorem der_32757 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32757 :=
  CNF.rup_sound cl_32757 [cl_27227,cl_32725] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27227 v h) (hints_cons _ _ _ (der_32725 v h) (by intro d hd; cases hd)))
def cl_32759 : CNF.NClause := [(60,false),(74,true),(62,true),(86,false),(80,false),(68,false)]
theorem der_32759 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32759 :=
  CNF.rup_sound cl_32759 [cl_27229,cl_32719] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27229 v h) (hints_cons _ _ _ (der_32719 v h) (by intro d hd; cases hd)))
def cl_32760 : CNF.NClause := [(60,false),(74,true),(29,false),(62,false),(86,false),(80,false)]
theorem der_32760 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32760 :=
  CNF.rup_sound cl_32760 [cl_27230,cl_27226] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27230 v h) (hints_cons _ _ _ (der_27226 v h) (by intro d hd; cases hd)))
def cl_32761 : CNF.NClause := [(60,false),(86,false),(74,true),(68,true),(62,false),(80,false)]
theorem der_32761 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32761 :=
  CNF.rup_sound cl_32761 [cl_27231,cl_32760] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27231 v h) (hints_cons _ _ _ (der_32760 v h) (by intro d hd; cases hd)))
def cl_32763 : CNF.NClause := [(60,false),(74,true),(62,true),(86,false),(80,false),(88,true)]
theorem der_32763 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32763 :=
  CNF.rup_sound cl_32763 [cl_27233,cl_32759] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27233 v h) (hints_cons _ _ _ (der_32759 v h) (by intro d hd; cases hd)))
def cl_32764 : CNF.NClause := [(60,false),(74,false),(62,false),(86,false),(29,true),(68,false)]
theorem der_32764 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32764 :=
  CNF.rup_sound cl_32764 [cl_27235,cl_32754] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27235 v h) (hints_cons _ _ _ (der_32754 v h) (by intro d hd; cases hd)))
def cl_32765 : CNF.NClause := [(60,false),(62,true),(29,false),(86,false),(74,false),(68,false)]
theorem der_32765 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32765 :=
  CNF.rup_sound cl_32765 [cl_27236,cl_32756] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27236 v h) (hints_cons _ _ _ (der_32756 v h) (by intro d hd; cases hd)))
def cl_32766 : CNF.NClause := [(60,false),(80,true),(62,true),(86,false),(74,false),(68,false)]
theorem der_32766 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32766 :=
  CNF.rup_sound cl_32766 [cl_27237,cl_32765] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27237 v h) (hints_cons _ _ _ (der_32765 v h) (by intro d hd; cases hd)))
def cl_32767 : CNF.NClause := [(60,false),(68,true),(29,false),(62,false),(86,false),(74,false)]
theorem der_32767 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32767 :=
  CNF.rup_sound cl_32767 [cl_27238,cl_27222] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27238 v h) (hints_cons _ _ _ (der_27222 v h) (by intro d hd; cases hd)))
def cl_32768 : CNF.NClause := [(60,false),(68,true),(80,true),(62,false),(86,false),(74,false)]
theorem der_32768 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32768 :=
  CNF.rup_sound cl_32768 [cl_27239,cl_27177] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27239 v h) (hints_cons _ _ _ (der_27177 v h) (by intro d hd; cases hd)))
def cl_32769 : CNF.NClause := [(60,false),(62,true),(29,false),(86,false),(74,false),(88,true)]
theorem der_32769 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32769 :=
  CNF.rup_sound cl_32769 [cl_27240,cl_32765] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27240 v h) (hints_cons _ _ _ (der_32765 v h) (by intro d hd; cases hd)))
def cl_32770 : CNF.NClause := [(60,false),(62,true),(88,true),(80,true),(86,false),(74,false)]
theorem der_32770 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32770 :=
  CNF.rup_sound cl_32770 [cl_27241,cl_32769] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27241 v h) (hints_cons _ _ _ (der_32769 v h) (by intro d hd; cases hd)))
def cl_32772 : CNF.NClause := [(60,false),(74,true),(80,true),(62,false),(86,false),(68,false)]
theorem der_32772 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32772 :=
  CNF.rup_sound cl_32772 [cl_27243,cl_32725] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27243 v h) (hints_cons _ _ _ (der_32725 v h) (by intro d hd; cases hd)))
def cl_32773 : CNF.NClause := [(60,false),(62,true),(80,true),(29,false),(86,false),(68,false)]
theorem der_32773 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32773 :=
  CNF.rup_sound cl_32773 [cl_27244,cl_32765] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27244 v h) (hints_cons _ _ _ (der_32765 v h) (by intro d hd; cases hd)))
def cl_32774 : CNF.NClause := [(60,false),(86,false),(62,true),(80,true),(68,false),(88,true)]
theorem der_32774 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32774 :=
  CNF.rup_sound cl_32774 [cl_27245,cl_32773] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27245 v h) (hints_cons _ _ _ (der_32773 v h) (by intro d hd; cases hd)))
def cl_32775 : CNF.NClause := [(60,false),(74,true),(29,false),(62,false),(86,false),(88,true)]
theorem der_32775 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32775 :=
  CNF.rup_sound cl_32775 [cl_27246,cl_32760] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27246 v h) (hints_cons _ _ _ (der_32760 v h) (by intro d hd; cases hd)))
def cl_32776 : CNF.NClause := [(60,false),(80,true),(68,true),(29,true),(62,false),(86,false)]
theorem der_32776 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32776 :=
  CNF.rup_sound cl_32776 [cl_27247,cl_32768] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27247 v h) (hints_cons _ _ _ (der_32768 v h) (by intro d hd; cases hd)))
def cl_32778 : CNF.NClause := [(60,false),(62,false),(29,true),(74,false),(80,false),(68,false)]
theorem der_32778 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32778 :=
  CNF.rup_sound cl_32778 [cl_27251,cl_27219] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27251 v h) (hints_cons _ _ _ (der_27219 v h) (by intro d hd; cases hd)))
def cl_32779 : CNF.NClause := [(60,false),(62,true),(29,false),(74,false),(80,false),(68,false)]
theorem der_32779 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32779 :=
  CNF.rup_sound cl_32779 [cl_27252,cl_32765] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27252 v h) (hints_cons _ _ _ (der_32765 v h) (by intro d hd; cases hd)))
def cl_32780 : CNF.NClause := [(60,false),(29,true),(86,true),(74,false),(80,false),(68,false)]
theorem der_32780 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32780 :=
  CNF.rup_sound cl_32780 [cl_27253,cl_32778] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27253 v h) (hints_cons _ _ _ (der_32778 v h) (by intro d hd; cases hd)))
def cl_32781 : CNF.NClause := [(60,false),(68,true),(29,false),(62,false),(74,false),(80,false)]
theorem der_32781 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32781 :=
  CNF.rup_sound cl_32781 [cl_27254,cl_32767] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27254 v h) (hints_cons _ _ _ (der_32767 v h) (by intro d hd; cases hd)))
def cl_32783 : CNF.NClause := [(60,false),(68,true),(86,true),(29,false),(74,false),(80,false)]
theorem der_32783 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32783 :=
  CNF.rup_sound cl_32783 [cl_27256,cl_32781] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27256 v h) (hints_cons _ _ _ (der_32781 v h) (by intro d hd; cases hd)))
def cl_32784 : CNF.NClause := [(60,false),(68,true),(86,true),(74,false),(80,false),(88,true)]
theorem der_32784 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32784 :=
  CNF.rup_sound cl_32784 [cl_27257,cl_32783] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27257 v h) (hints_cons _ _ _ (der_32783 v h) (by intro d hd; cases hd)))
def cl_32785 : CNF.NClause := [(60,false),(74,true),(29,false),(62,false),(80,false),(68,false)]
theorem der_32785 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32785 :=
  CNF.rup_sound cl_32785 [cl_27258,cl_32760] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27258 v h) (hints_cons _ _ _ (der_32760 v h) (by intro d hd; cases hd)))
def cl_32786 : CNF.NClause := [(60,false),(29,true),(86,true),(62,false),(80,false),(68,false)]
theorem der_32786 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32786 :=
  CNF.rup_sound cl_32786 [cl_27259,cl_32778] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27259 v h) (hints_cons _ _ _ (der_32778 v h) (by intro d hd; cases hd)))
def cl_32788 : CNF.NClause := [(60,false),(74,true),(62,true),(86,true),(80,false),(68,false)]
theorem der_32788 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32788 :=
  CNF.rup_sound cl_32788 [cl_27261,cl_32735] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27261 v h) (hints_cons _ _ _ (der_32735 v h) (by intro d hd; cases hd)))
def cl_32789 : CNF.NClause := [(60,false),(74,true),(86,true),(29,false),(62,false),(80,false)]
theorem der_32789 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32789 :=
  CNF.rup_sound cl_32789 [cl_27262,cl_32750] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27262 v h) (hints_cons _ _ _ (der_32750 v h) (by intro d hd; cases hd)))
def cl_32790 : CNF.NClause := [(60,false),(62,false),(74,true),(68,true),(29,true),(80,false)]
theorem der_32790 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32790 :=
  CNF.rup_sound cl_32790 [cl_27263,cl_32761] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27263 v h) (hints_cons _ _ _ (der_32761 v h) (by intro d hd; cases hd)))
def cl_32792 : CNF.NClause := [(60,false),(68,true),(62,true),(86,true),(80,false),(88,true)]
theorem der_32792 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32792 :=
  CNF.rup_sound cl_32792 [cl_27265,cl_32784] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27265 v h) (hints_cons _ _ _ (der_32784 v h) (by intro d hd; cases hd)))
def cl_32793 : CNF.NClause := [(60,false),(86,true),(29,false),(62,false),(74,false),(68,false)]
theorem der_32793 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32793 :=
  CNF.rup_sound cl_32793 [cl_27266,cl_27250] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27266 v h) (hints_cons _ _ _ (der_27250 v h) (by intro d hd; cases hd)))
def cl_32794 : CNF.NClause := [(60,false),(62,true),(80,true),(29,false),(74,false),(68,false)]
theorem der_32794 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32794 :=
  CNF.rup_sound cl_32794 [cl_27268,cl_32765] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27268 v h) (hints_cons _ _ _ (der_32765 v h) (by intro d hd; cases hd)))
def cl_32795 : CNF.NClause := [(60,false),(80,true),(62,true),(74,false),(68,false),(88,true)]
theorem der_32795 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32795 :=
  CNF.rup_sound cl_32795 [cl_27269,cl_32794] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27269 v h) (hints_cons _ _ _ (der_32794 v h) (by intro d hd; cases hd)))
def cl_32796 : CNF.NClause := [(60,false),(68,true),(86,true),(29,false),(62,false),(74,false)]
theorem der_32796 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32796 :=
  CNF.rup_sound cl_32796 [cl_27270,cl_32742] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27270 v h) (hints_cons _ _ _ (der_32742 v h) (by intro d hd; cases hd)))
def cl_32797 : CNF.NClause := [(60,false),(68,true),(86,true),(80,true),(62,false),(74,false)]
theorem der_32797 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32797 :=
  CNF.rup_sound cl_32797 [cl_27271,cl_32743] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27271 v h) (hints_cons _ _ _ (der_32743 v h) (by intro d hd; cases hd)))
def cl_32798 : CNF.NClause := [(60,false),(68,true),(62,true),(86,true),(29,false),(74,false)]
theorem der_32798 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32798 :=
  CNF.rup_sound cl_32798 [cl_27272,cl_32783] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27272 v h) (hints_cons _ _ _ (der_32783 v h) (by intro d hd; cases hd)))
def cl_32799 : CNF.NClause := [(60,false),(74,false),(68,true),(86,true),(80,true),(29,true)]
theorem der_32799 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32799 :=
  CNF.rup_sound cl_32799 [cl_27273,cl_32797] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27273 v h) (hints_cons _ _ _ (der_32797 v h) (by intro d hd; cases hd)))
def cl_32800 : CNF.NClause := [(60,false),(74,true),(80,true),(29,false),(62,false),(68,false)]
theorem der_32800 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32800 :=
  CNF.rup_sound cl_32800 [cl_27274,cl_32772] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27274 v h) (hints_cons _ _ _ (der_32772 v h) (by intro d hd; cases hd)))
def cl_32801 : CNF.NClause := [(60,false),(74,true),(29,true),(86,true),(62,false),(68,false)]
theorem der_32801 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32801 :=
  CNF.rup_sound cl_32801 [cl_27275,cl_32786] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27275 v h) (hints_cons _ _ _ (der_32786 v h) (by intro d hd; cases hd)))
def cl_32802 : CNF.NClause := [(60,false),(74,true),(62,true),(86,true),(29,false),(68,false)]
theorem der_32802 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32802 :=
  CNF.rup_sound cl_32802 [cl_27276,cl_32748] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27276 v h) (hints_cons _ _ _ (der_32748 v h) (by intro d hd; cases hd)))
def cl_32804 : CNF.NClause := [(60,false),(74,true),(68,true),(29,true),(62,false),(88,true)]
theorem der_32804 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32804 :=
  CNF.rup_sound cl_32804 [cl_27279,cl_32790] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27279 v h) (hints_cons _ _ _ (der_32790 v h) (by intro d hd; cases hd)))
def cl_32805 : CNF.NClause := [(60,false),(74,true),(68,true),(62,true),(86,true),(88,true)]
theorem der_32805 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32805 :=
  CNF.rup_sound cl_32805 [cl_27281,cl_32792] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27281 v h) (hints_cons _ _ _ (der_32792 v h) (by intro d hd; cases hd)))
def cl_32807 : CNF.NClause := [(55,false),(91,false),(63,true),(84,false),(76,false),(80,false)]
theorem der_32807 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32807 :=
  CNF.rup_sound cl_32807 [cl_27285,cl_27282] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27285 v h) (hints_cons _ _ _ (der_27282 v h) (by intro d hd; cases hd)))
def cl_32809 : CNF.NClause := [(55,false),(84,false),(76,true),(91,false),(63,false),(80,false)]
theorem der_32809 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32809 :=
  CNF.rup_sound cl_32809 [cl_27290,cl_27289] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27290 v h) (hints_cons _ _ _ (der_27289 v h) (by intro d hd; cases hd)))
def cl_32811 : CNF.NClause := [(55,false),(63,true),(91,false),(67,false),(84,false),(76,false)]
theorem der_32811 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32811 :=
  CNF.rup_sound cl_32811 [cl_27295,cl_27282] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27295 v h) (hints_cons _ _ _ (der_27282 v h) (by intro d hd; cases hd)))
def cl_32812 : CNF.NClause := [(55,false),(91,false),(63,false),(84,false),(76,false),(67,true)]
theorem der_32812 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32812 :=
  CNF.rup_sound cl_32812 [cl_27297,cl_27283] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27297 v h) (hints_cons _ _ _ (der_27283 v h) (by intro d hd; cases hd)))
def cl_32813 : CNF.NClause := [(55,false),(24,false),(63,true),(91,false),(84,false),(76,false)]
theorem der_32813 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32813 :=
  CNF.rup_sound cl_32813 [cl_27298,cl_27284] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27298 v h) (hints_cons _ _ _ (der_27284 v h) (by intro d hd; cases hd)))
def cl_32814 : CNF.NClause := [(55,false),(91,false),(24,true),(63,true),(84,false),(76,false)]
theorem der_32814 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32814 :=
  CNF.rup_sound cl_32814 [cl_27299,cl_32807] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27299 v h) (hints_cons _ _ _ (der_32807 v h) (by intro d hd; cases hd)))
def cl_32815 : CNF.NClause := [(55,false),(76,true),(91,false),(63,false),(67,false),(84,false)]
theorem der_32815 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32815 :=
  CNF.rup_sound cl_32815 [cl_27301,cl_27300] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27301 v h) (hints_cons _ _ _ (der_27300 v h) (by intro d hd; cases hd)))
def cl_32816 : CNF.NClause := [(55,false),(91,false),(80,true),(63,true),(67,false),(84,false)]
theorem der_32816 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32816 :=
  CNF.rup_sound cl_32816 [cl_27303,cl_27302] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27303 v h) (hints_cons _ _ _ (der_27302 v h) (by intro d hd; cases hd)))
def cl_32817 : CNF.NClause := [(55,false),(84,false),(76,true),(91,false),(24,false),(63,false)]
theorem der_32817 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32817 :=
  CNF.rup_sound cl_32817 [cl_27304,cl_32809] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27304 v h) (hints_cons _ _ _ (der_32809 v h) (by intro d hd; cases hd)))
def cl_32818 : CNF.NClause := [(55,false),(84,false),(76,true),(91,false),(63,false),(24,true)]
theorem der_32818 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32818 :=
  CNF.rup_sound cl_32818 [cl_27305,cl_32815] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27305 v h) (hints_cons _ _ _ (der_32815 v h) (by intro d hd; cases hd)))
def cl_32819 : CNF.NClause := [(55,false),(84,false),(76,true),(80,true),(24,false),(91,false)]
theorem der_32819 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32819 :=
  CNF.rup_sound cl_32819 [cl_27306,cl_32817] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27306 v h) (hints_cons _ _ _ (der_32817 v h) (by intro d hd; cases hd)))
def cl_32820 : CNF.NClause := [(55,false),(84,false),(63,true),(91,false),(24,true),(67,true)]
theorem der_32820 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32820 :=
  CNF.rup_sound cl_32820 [cl_27307,cl_32814] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27307 v h) (hints_cons _ _ _ (der_32814 v h) (by intro d hd; cases hd)))
def cl_32821 : CNF.NClause := [(55,false),(80,false),(84,true),(91,false),(67,false),(76,false)]
theorem der_32821 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32821 :=
  CNF.rup_sound cl_32821 [cl_27310,cl_27309] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27310 v h) (hints_cons _ _ _ (der_27309 v h) (by intro d hd; cases hd)))
def cl_32822 : CNF.NClause := [(55,false),(84,true),(91,false),(63,false),(76,false),(80,false)]
theorem der_32822 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32822 :=
  CNF.rup_sound cl_32822 [cl_27312,cl_27311] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27312 v h) (hints_cons _ _ _ (der_27311 v h) (by intro d hd; cases hd)))
def cl_32823 : CNF.NClause := [(55,false),(84,true),(24,false),(91,false),(76,false),(80,false)]
theorem der_32823 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32823 :=
  CNF.rup_sound cl_32823 [cl_27313,cl_27311] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27313 v h) (hints_cons _ _ _ (der_27311 v h) (by intro d hd; cases hd)))
def cl_32825 : CNF.NClause := [(55,false),(80,false),(76,true),(91,false),(63,false),(67,false)]
theorem der_32825 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32825 :=
  CNF.rup_sound cl_32825 [cl_27316,cl_27315] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27316 v h) (hints_cons _ _ _ (der_27315 v h) (by intro d hd; cases hd)))
def cl_32828 : CNF.NClause := [(55,false),(76,true),(91,false),(63,false),(80,false),(67,true)]
theorem der_32828 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32828 :=
  CNF.rup_sound cl_32828 [cl_27320,cl_32809] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27320 v h) (hints_cons _ _ _ (der_32809 v h) (by intro d hd; cases hd)))
def cl_32829 : CNF.NClause := [(55,false),(63,true),(84,true),(91,false),(80,false),(24,false)]
theorem der_32829 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32829 :=
  CNF.rup_sound cl_32829 [cl_27321,cl_27317] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27321 v h) (hints_cons _ _ _ (der_27317 v h) (by intro d hd; cases hd)))
def cl_32830 : CNF.NClause := [(55,false),(80,false),(76,true),(63,true),(84,true),(91,false)]
theorem der_32830 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32830 :=
  CNF.rup_sound cl_32830 [cl_27322,cl_32829] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27322 v h) (hints_cons _ _ _ (der_32829 v h) (by intro d hd; cases hd)))
def cl_32831 : CNF.NClause := [(55,false),(76,false),(80,true),(91,false),(67,false),(24,false)]
theorem der_32831 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32831 :=
  CNF.rup_sound cl_32831 [cl_27325,cl_27323] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27325 v h) (hints_cons _ _ _ (der_27323 v h) (by intro d hd; cases hd)))
def cl_32832 : CNF.NClause := [(55,false),(76,false),(80,true),(63,true),(91,false),(67,false)]
theorem der_32832 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32832 :=
  CNF.rup_sound cl_32832 [cl_27326,cl_32831] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27326 v h) (hints_cons _ _ _ (der_32831 v h) (by intro d hd; cases hd)))
def cl_32833 : CNF.NClause := [(55,false),(80,true),(91,false),(63,false),(76,false),(24,false)]
theorem der_32833 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32833 :=
  CNF.rup_sound cl_32833 [cl_27327,cl_27323] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27327 v h) (hints_cons _ _ _ (der_27323 v h) (by intro d hd; cases hd)))
def cl_32834 : CNF.NClause := [(55,false),(80,true),(67,true),(91,false),(63,false),(76,false)]
theorem der_32834 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32834 :=
  CNF.rup_sound cl_32834 [cl_27328,cl_32833] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27328 v h) (hints_cons _ _ _ (der_32833 v h) (by intro d hd; cases hd)))
def cl_32835 : CNF.NClause := [(55,false),(67,true),(63,true),(91,false),(76,false),(24,false)]
theorem der_32835 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32835 :=
  CNF.rup_sound cl_32835 [cl_27329,cl_32813] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27329 v h) (hints_cons _ _ _ (der_32813 v h) (by intro d hd; cases hd)))
def cl_32836 : CNF.NClause := [(55,false),(67,true),(63,true),(84,true),(91,false),(76,false)]
theorem der_32836 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32836 :=
  CNF.rup_sound cl_32836 [cl_27330,cl_32835] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27330 v h) (hints_cons _ _ _ (der_32835 v h) (by intro d hd; cases hd)))
def cl_32837 : CNF.NClause := [(55,false),(76,true),(67,false),(91,false),(63,false),(24,false)]
theorem der_32837 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32837 :=
  CNF.rup_sound cl_32837 [cl_27331,cl_27315] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27331 v h) (hints_cons _ _ _ (der_27315 v h) (by intro d hd; cases hd)))
def cl_32838 : CNF.NClause := [(55,false),(76,true),(67,false),(80,true),(91,false),(63,false)]
theorem der_32838 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32838 :=
  CNF.rup_sound cl_32838 [cl_27332,cl_32837] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27332 v h) (hints_cons _ _ _ (der_32837 v h) (by intro d hd; cases hd)))
def cl_32839 : CNF.NClause := [(55,false),(80,true),(67,false),(63,true),(91,false),(24,false)]
theorem der_32839 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32839 :=
  CNF.rup_sound cl_32839 [cl_27333,cl_32816] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27333 v h) (hints_cons _ _ _ (der_32816 v h) (by intro d hd; cases hd)))
def cl_32840 : CNF.NClause := [(55,false),(76,true),(84,true),(91,false),(24,false),(63,false)]
theorem der_32840 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32840 :=
  CNF.rup_sound cl_32840 [cl_27335,cl_32837] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27335 v h) (hints_cons _ _ _ (der_32837 v h) (by intro d hd; cases hd)))
def cl_32841 : CNF.NClause := [(55,false),(76,true),(84,true),(91,false),(63,false),(67,true)]
theorem der_32841 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32841 :=
  CNF.rup_sound cl_32841 [cl_27336,cl_32828] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27336 v h) (hints_cons _ _ _ (der_32828 v h) (by intro d hd; cases hd)))
def cl_32842 : CNF.NClause := [(55,false),(91,false),(76,true),(80,true),(24,false),(67,true)]
theorem der_32842 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32842 :=
  CNF.rup_sound cl_32842 [cl_27337,cl_32819] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27337 v h) (hints_cons _ _ _ (der_32819 v h) (by intro d hd; cases hd)))
def cl_32843 : CNF.NClause := [(55,false),(84,true),(76,true),(63,true),(24,true),(91,false)]
theorem der_32843 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32843 :=
  CNF.rup_sound cl_32843 [cl_27338,cl_32830] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27338 v h) (hints_cons _ _ _ (der_32830 v h) (by intro d hd; cases hd)))
def cl_32844 : CNF.NClause := [(55,false),(67,false),(24,true),(84,false),(76,false),(80,false)]
theorem der_32844 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32844 :=
  CNF.rup_sound cl_32844 [cl_27341,cl_27339] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27341 v h) (hints_cons _ _ _ (der_27339 v h) (by intro d hd; cases hd)))
def cl_32845 : CNF.NClause := [(55,false),(80,false),(84,false),(76,false),(63,false),(67,true)]
theorem der_32845 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32845 :=
  CNF.rup_sound cl_32845 [cl_27343,cl_27283] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27343 v h) (hints_cons _ _ _ (der_27283 v h) (by intro d hd; cases hd)))
def cl_32846 : CNF.NClause := [(55,false),(84,false),(24,true),(76,false),(80,false),(67,true)]
theorem der_32846 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32846 :=
  CNF.rup_sound cl_32846 [cl_27345,cl_32845] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27345 v h) (hints_cons _ _ _ (der_32845 v h) (by intro d hd; cases hd)))
def cl_32847 : CNF.NClause := [(55,false),(24,true),(63,false),(67,false),(84,false),(80,false)]
theorem der_32847 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32847 :=
  CNF.rup_sound cl_32847 [cl_27347,cl_27339] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27347 v h) (hints_cons _ _ _ (der_27339 v h) (by intro d hd; cases hd)))
def cl_32848 : CNF.NClause := [(55,false),(76,true),(24,false),(67,false),(84,false),(80,false)]
theorem der_32848 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32848 :=
  CNF.rup_sound cl_32848 [cl_27348,cl_27346] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27348 v h) (hints_cons _ _ _ (der_27346 v h) (by intro d hd; cases hd)))
def cl_32849 : CNF.NClause := [(55,false),(24,true),(63,true),(67,false),(84,false),(80,false)]
theorem der_32849 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32849 :=
  CNF.rup_sound cl_32849 [cl_27349,cl_32844] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27349 v h) (hints_cons _ _ _ (der_32844 v h) (by intro d hd; cases hd)))
def cl_32850 : CNF.NClause := [(55,false),(76,true),(24,false),(63,false),(84,false),(80,false)]
theorem der_32850 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32850 :=
  CNF.rup_sound cl_32850 [cl_27350,cl_27346] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27350 v h) (hints_cons _ _ _ (der_27346 v h) (by intro d hd; cases hd)))
def cl_32851 : CNF.NClause := [(55,false),(76,true),(63,false),(84,false),(80,false),(67,true)]
theorem der_32851 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32851 :=
  CNF.rup_sound cl_32851 [cl_27351,cl_32809] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27351 v h) (hints_cons _ _ _ (der_32809 v h) (by intro d hd; cases hd)))
def cl_32852 : CNF.NClause := [(55,false),(91,true),(84,false),(80,false),(24,false),(67,true)]
theorem der_32852 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32852 :=
  CNF.rup_sound cl_32852 [cl_27352,cl_27344] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27352 v h) (hints_cons _ _ _ (der_27344 v h) (by intro d hd; cases hd)))
def cl_32853 : CNF.NClause := [(55,false),(80,false),(63,true),(84,false),(24,true),(67,true)]
theorem der_32853 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32853 :=
  CNF.rup_sound cl_32853 [cl_27353,cl_32846] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27353 v h) (hints_cons _ _ _ (der_32846 v h) (by intro d hd; cases hd)))
def cl_32854 : CNF.NClause := [(55,false),(84,false),(63,false),(24,true),(67,false),(76,false)]
theorem der_32854 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32854 :=
  CNF.rup_sound cl_32854 [cl_27355,cl_27339] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27355 v h) (hints_cons _ _ _ (der_27339 v h) (by intro d hd; cases hd)))
def cl_32855 : CNF.NClause := [(55,false),(24,false),(63,true),(67,false),(84,false),(76,false)]
theorem der_32855 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32855 :=
  CNF.rup_sound cl_32855 [cl_27356,cl_27340] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27356 v h) (hints_cons _ _ _ (der_27340 v h) (by intro d hd; cases hd)))
def cl_32856 : CNF.NClause := [(55,false),(80,true),(63,true),(67,false),(84,false),(76,false)]
theorem der_32856 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32856 :=
  CNF.rup_sound cl_32856 [cl_27357,cl_32855] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27357 v h) (hints_cons _ _ _ (der_32855 v h) (by intro d hd; cases hd)))
def cl_32857 : CNF.NClause := [(55,false),(24,false),(63,false),(84,false),(76,false),(67,true)]
theorem der_32857 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32857 :=
  CNF.rup_sound cl_32857 [cl_27358,cl_27342] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27358 v h) (hints_cons _ _ _ (der_27342 v h) (by intro d hd; cases hd)))
def cl_32858 : CNF.NClause := [(55,false),(80,true),(24,false),(63,true),(84,false),(76,false)]
theorem der_32858 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32858 :=
  CNF.rup_sound cl_32858 [cl_27360,cl_32813] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27360 v h) (hints_cons _ _ _ (der_32813 v h) (by intro d hd; cases hd)))
def cl_32859 : CNF.NClause := [(55,false),(80,true),(24,true),(63,true),(84,false),(76,false)]
theorem der_32859 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32859 :=
  CNF.rup_sound cl_32859 [cl_27361,cl_32856] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27361 v h) (hints_cons _ _ _ (der_32856 v h) (by intro d hd; cases hd)))
def cl_32860 : CNF.NClause := [(55,false),(24,false),(80,true),(63,false),(67,false),(84,false)]
theorem der_32860 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32860 :=
  CNF.rup_sound cl_32860 [cl_27362,cl_27354] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27362 v h) (hints_cons _ _ _ (der_27354 v h) (by intro d hd; cases hd)))
def cl_32861 : CNF.NClause := [(55,false),(84,false),(80,true),(63,false),(67,false),(91,true)]
theorem der_32861 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : CNF.Holds (v ∘ decodeVar) cl_32861 :=
  CNF.rup_sound cl_32861 [cl_27363,cl_32860] (by decide) (v ∘ decodeVar) (hints_cons _ _ _ (der_27363 v h) (hints_cons _ _ _ (der_32860 v h) (by intro d hd; cases hd)))
def chunk019 : List CNF.NClause := [cl_32303,cl_32304,cl_32305,cl_32306,cl_32307,cl_32308,cl_32309,cl_32310,cl_32311,cl_32312,cl_32313,cl_32314,cl_32315,cl_32316,cl_32317,cl_32318,cl_32319,cl_32320,cl_32321,cl_32322,cl_32323,cl_32324,cl_32325,cl_32326,cl_32327,cl_32328,cl_32329,cl_32330,cl_32331,cl_32332,cl_32333,cl_32334,cl_32335,cl_32336,cl_32338,cl_32339,cl_32340,cl_32341,cl_32342,cl_32343,cl_32344,cl_32345,cl_32346,cl_32347,cl_32348,cl_32349,cl_32350,cl_32351,cl_32352,cl_32353,cl_32354,cl_32356,cl_32358,cl_32360,cl_32361,cl_32362,cl_32363,cl_32364,cl_32365,cl_32366,cl_32367,cl_32368,cl_32369,cl_32370,cl_32371,cl_32372,cl_32373,cl_32374,cl_32375,cl_32376,cl_32377,cl_32378,cl_32379,cl_32380,cl_32381,cl_32382,cl_32384,cl_32385,cl_32386,cl_32387,cl_32388,cl_32389,cl_32390,cl_32391,cl_32392,cl_32393,cl_32394,cl_32395,cl_32396,cl_32397,cl_32398,cl_32399,cl_32402,cl_32403,cl_32404,cl_32405,cl_32406,cl_32407,cl_32408,cl_32409,cl_32410,cl_32411,cl_32412,cl_32413,cl_32414,cl_32416,cl_32417,cl_32418,cl_32419,cl_32420,cl_32421,cl_32422,cl_32423,cl_32424,cl_32425,cl_32427,cl_32428,cl_32429,cl_32430,cl_32431,cl_32433,cl_32435,cl_32436,cl_32437,cl_32438,cl_32440,cl_32441,cl_32442,cl_32443,cl_32445,cl_32446,cl_32447,cl_32448,cl_32449,cl_32450,cl_32451,cl_32452,cl_32453,cl_32454,cl_32455,cl_32456,cl_32457,cl_32458,cl_32459,cl_32460,cl_32461,cl_32462,cl_32463,cl_32464,cl_32466,cl_32467,cl_32468,cl_32469,cl_32470,cl_32471,cl_32472,cl_32473,cl_32474,cl_32475,cl_32476,cl_32477,cl_32478,cl_32479,cl_32480,cl_32481,cl_32482,cl_32484,cl_32485,cl_32486,cl_32487,cl_32488,cl_32489,cl_32490,cl_32491,cl_32492,cl_32494,cl_32495,cl_32496,cl_32498,cl_32499,cl_32500,cl_32501,cl_32502,cl_32504,cl_32505,cl_32507,cl_32508,cl_32509,cl_32510,cl_32511,cl_32512,cl_32513,cl_32514,cl_32515,cl_32516,cl_32517,cl_32518,cl_32519,cl_32520,cl_32521,cl_32522,cl_32523,cl_32524,cl_32526,cl_32527,cl_32528,cl_32529,cl_32530,cl_32531,cl_32532,cl_32533,cl_32535,cl_32536,cl_32537,cl_32538,cl_32539,cl_32540,cl_32541,cl_32542,cl_32543,cl_32544,cl_32545,cl_32547,cl_32548,cl_32549,cl_32550,cl_32551,cl_32552,cl_32553,cl_32555,cl_32556,cl_32557,cl_32558,cl_32559,cl_32560,cl_32561,cl_32563,cl_32564,cl_32565,cl_32567,cl_32568,cl_32569,cl_32571,cl_32572,cl_32574,cl_32575,cl_32576,cl_32577,cl_32578,cl_32579,cl_32580,cl_32581,cl_32582,cl_32583,cl_32584,cl_32585,cl_32586,cl_32587,cl_32588,cl_32589,cl_32591,cl_32592,cl_32593,cl_32594,cl_32595,cl_32596,cl_32597,cl_32598,cl_32599,cl_32600,cl_32601,cl_32602,cl_32603,cl_32604,cl_32605,cl_32606,cl_32607,cl_32608,cl_32609,cl_32610,cl_32612,cl_32613,cl_32614,cl_32615,cl_32616,cl_32617,cl_32618,cl_32619,cl_32620,cl_32621,cl_32622,cl_32624,cl_32626,cl_32628,cl_32629,cl_32631,cl_32632,cl_32633,cl_32634,cl_32636,cl_32637,cl_32638,cl_32639,cl_32640,cl_32641,cl_32642,cl_32643,cl_32644,cl_32645,cl_32646,cl_32647,cl_32649,cl_32650,cl_32651,cl_32653,cl_32654,cl_32655,cl_32656,cl_32657,cl_32658,cl_32659,cl_32660,cl_32661,cl_32662,cl_32663,cl_32664,cl_32665,cl_32666,cl_32667,cl_32668,cl_32669,cl_32670,cl_32671,cl_32672,cl_32673,cl_32674,cl_32675,cl_32676,cl_32677,cl_32678,cl_32679,cl_32680,cl_32681,cl_32682,cl_32683,cl_32684,cl_32685,cl_32686,cl_32687,cl_32688,cl_32689,cl_32690,cl_32691,cl_32692,cl_32693,cl_32694,cl_32695,cl_32696,cl_32697,cl_32698,cl_32699,cl_32700,cl_32701,cl_32702,cl_32703,cl_32704,cl_32705,cl_32706,cl_32707,cl_32709,cl_32710,cl_32711,cl_32713,cl_32714,cl_32715,cl_32717,cl_32719,cl_32721,cl_32722,cl_32723,cl_32724,cl_32725,cl_32727,cl_32728,cl_32730,cl_32731,cl_32732,cl_32733,cl_32734,cl_32735,cl_32736,cl_32737,cl_32738,cl_32740,cl_32741,cl_32742,cl_32743,cl_32744,cl_32745,cl_32746,cl_32748,cl_32749,cl_32750,cl_32751,cl_32752,cl_32753,cl_32754,cl_32755,cl_32756,cl_32757,cl_32759,cl_32760,cl_32761,cl_32763,cl_32764,cl_32765,cl_32766,cl_32767,cl_32768,cl_32769,cl_32770,cl_32772,cl_32773,cl_32774,cl_32775,cl_32776,cl_32778,cl_32779,cl_32780,cl_32781,cl_32783,cl_32784,cl_32785,cl_32786,cl_32788,cl_32789,cl_32790,cl_32792,cl_32793,cl_32794,cl_32795,cl_32796,cl_32797,cl_32798,cl_32799,cl_32800,cl_32801,cl_32802,cl_32804,cl_32805,cl_32807,cl_32809,cl_32811,cl_32812,cl_32813,cl_32814,cl_32815,cl_32816,cl_32817,cl_32818,cl_32819,cl_32820,cl_32821,cl_32822,cl_32823,cl_32825,cl_32828,cl_32829,cl_32830,cl_32831,cl_32832,cl_32833,cl_32834,cl_32835,cl_32836,cl_32837,cl_32838,cl_32839,cl_32840,cl_32841,cl_32842,cl_32843,cl_32844,cl_32845,cl_32846,cl_32847,cl_32848,cl_32849,cl_32850,cl_32851,cl_32852,cl_32853,cl_32854,cl_32855,cl_32856,cl_32857,cl_32858,cl_32859,cl_32860,cl_32861]
theorem chunk_sound019 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ chunk019, CNF.Holds (v ∘ decodeVar) c :=
  (hints_cons _ _ _ (der_32303 v h) (hints_cons _ _ _ (der_32304 v h) (hints_cons _ _ _ (der_32305 v h) (hints_cons _ _ _ (der_32306 v h) (hints_cons _ _ _ (der_32307 v h) (hints_cons _ _ _ (der_32308 v h) (hints_cons _ _ _ (der_32309 v h) (hints_cons _ _ _ (der_32310 v h) (hints_cons _ _ _ (der_32311 v h) (hints_cons _ _ _ (der_32312 v h) (hints_cons _ _ _ (der_32313 v h) (hints_cons _ _ _ (der_32314 v h) (hints_cons _ _ _ (der_32315 v h) (hints_cons _ _ _ (der_32316 v h) (hints_cons _ _ _ (der_32317 v h) (hints_cons _ _ _ (der_32318 v h) (hints_cons _ _ _ (der_32319 v h) (hints_cons _ _ _ (der_32320 v h) (hints_cons _ _ _ (der_32321 v h) (hints_cons _ _ _ (der_32322 v h) (hints_cons _ _ _ (der_32323 v h) (hints_cons _ _ _ (der_32324 v h) (hints_cons _ _ _ (der_32325 v h) (hints_cons _ _ _ (der_32326 v h) (hints_cons _ _ _ (der_32327 v h) (hints_cons _ _ _ (der_32328 v h) (hints_cons _ _ _ (der_32329 v h) (hints_cons _ _ _ (der_32330 v h) (hints_cons _ _ _ (der_32331 v h) (hints_cons _ _ _ (der_32332 v h) (hints_cons _ _ _ (der_32333 v h) (hints_cons _ _ _ (der_32334 v h) (hints_cons _ _ _ (der_32335 v h) (hints_cons _ _ _ (der_32336 v h) (hints_cons _ _ _ (der_32338 v h) (hints_cons _ _ _ (der_32339 v h) (hints_cons _ _ _ (der_32340 v h) (hints_cons _ _ _ (der_32341 v h) (hints_cons _ _ _ (der_32342 v h) (hints_cons _ _ _ (der_32343 v h) (hints_cons _ _ _ (der_32344 v h) (hints_cons _ _ _ (der_32345 v h) (hints_cons _ _ _ (der_32346 v h) (hints_cons _ _ _ (der_32347 v h) (hints_cons _ _ _ (der_32348 v h) (hints_cons _ _ _ (der_32349 v h) (hints_cons _ _ _ (der_32350 v h) (hints_cons _ _ _ (der_32351 v h) (hints_cons _ _ _ (der_32352 v h) (hints_cons _ _ _ (der_32353 v h) (hints_cons _ _ _ (der_32354 v h) (hints_cons _ _ _ (der_32356 v h) (hints_cons _ _ _ (der_32358 v h) (hints_cons _ _ _ (der_32360 v h) (hints_cons _ _ _ (der_32361 v h) (hints_cons _ _ _ (der_32362 v h) (hints_cons _ _ _ (der_32363 v h) (hints_cons _ _ _ (der_32364 v h) (hints_cons _ _ _ (der_32365 v h) (hints_cons _ _ _ (der_32366 v h) (hints_cons _ _ _ (der_32367 v h) (hints_cons _ _ _ (der_32368 v h) (hints_cons _ _ _ (der_32369 v h) (hints_cons _ _ _ (der_32370 v h) (hints_cons _ _ _ (der_32371 v h) (hints_cons _ _ _ (der_32372 v h) (hints_cons _ _ _ (der_32373 v h) (hints_cons _ _ _ (der_32374 v h) (hints_cons _ _ _ (der_32375 v h) (hints_cons _ _ _ (der_32376 v h) (hints_cons _ _ _ (der_32377 v h) (hints_cons _ _ _ (der_32378 v h) (hints_cons _ _ _ (der_32379 v h) (hints_cons _ _ _ (der_32380 v h) (hints_cons _ _ _ (der_32381 v h) (hints_cons _ _ _ (der_32382 v h) (hints_cons _ _ _ (der_32384 v h) (hints_cons _ _ _ (der_32385 v h) (hints_cons _ _ _ (der_32386 v h) (hints_cons _ _ _ (der_32387 v h) (hints_cons _ _ _ (der_32388 v h) (hints_cons _ _ _ (der_32389 v h) (hints_cons _ _ _ (der_32390 v h) (hints_cons _ _ _ (der_32391 v h) (hints_cons _ _ _ (der_32392 v h) (hints_cons _ _ _ (der_32393 v h) (hints_cons _ _ _ (der_32394 v h) (hints_cons _ _ _ (der_32395 v h) (hints_cons _ _ _ (der_32396 v h) (hints_cons _ _ _ (der_32397 v h) (hints_cons _ _ _ (der_32398 v h) (hints_cons _ _ _ (der_32399 v h) (hints_cons _ _ _ (der_32402 v h) (hints_cons _ _ _ (der_32403 v h) (hints_cons _ _ _ (der_32404 v h) (hints_cons _ _ _ (der_32405 v h) (hints_cons _ _ _ (der_32406 v h) (hints_cons _ _ _ (der_32407 v h) (hints_cons _ _ _ (der_32408 v h) (hints_cons _ _ _ (der_32409 v h) (hints_cons _ _ _ (der_32410 v h) (hints_cons _ _ _ (der_32411 v h) (hints_cons _ _ _ (der_32412 v h) (hints_cons _ _ _ (der_32413 v h) (hints_cons _ _ _ (der_32414 v h) (hints_cons _ _ _ (der_32416 v h) (hints_cons _ _ _ (der_32417 v h) (hints_cons _ _ _ (der_32418 v h) (hints_cons _ _ _ (der_32419 v h) (hints_cons _ _ _ (der_32420 v h) (hints_cons _ _ _ (der_32421 v h) (hints_cons _ _ _ (der_32422 v h) (hints_cons _ _ _ (der_32423 v h) (hints_cons _ _ _ (der_32424 v h) (hints_cons _ _ _ (der_32425 v h) (hints_cons _ _ _ (der_32427 v h) (hints_cons _ _ _ (der_32428 v h) (hints_cons _ _ _ (der_32429 v h) (hints_cons _ _ _ (der_32430 v h) (hints_cons _ _ _ (der_32431 v h) (hints_cons _ _ _ (der_32433 v h) (hints_cons _ _ _ (der_32435 v h) (hints_cons _ _ _ (der_32436 v h) (hints_cons _ _ _ (der_32437 v h) (hints_cons _ _ _ (der_32438 v h) (hints_cons _ _ _ (der_32440 v h) (hints_cons _ _ _ (der_32441 v h) (hints_cons _ _ _ (der_32442 v h) (hints_cons _ _ _ (der_32443 v h) (hints_cons _ _ _ (der_32445 v h) (hints_cons _ _ _ (der_32446 v h) (hints_cons _ _ _ (der_32447 v h) (hints_cons _ _ _ (der_32448 v h) (hints_cons _ _ _ (der_32449 v h) (hints_cons _ _ _ (der_32450 v h) (hints_cons _ _ _ (der_32451 v h) (hints_cons _ _ _ (der_32452 v h) (hints_cons _ _ _ (der_32453 v h) (hints_cons _ _ _ (der_32454 v h) (hints_cons _ _ _ (der_32455 v h) (hints_cons _ _ _ (der_32456 v h) (hints_cons _ _ _ (der_32457 v h) (hints_cons _ _ _ (der_32458 v h) (hints_cons _ _ _ (der_32459 v h) (hints_cons _ _ _ (der_32460 v h) (hints_cons _ _ _ (der_32461 v h) (hints_cons _ _ _ (der_32462 v h) (hints_cons _ _ _ (der_32463 v h) (hints_cons _ _ _ (der_32464 v h) (hints_cons _ _ _ (der_32466 v h) (hints_cons _ _ _ (der_32467 v h) (hints_cons _ _ _ (der_32468 v h) (hints_cons _ _ _ (der_32469 v h) (hints_cons _ _ _ (der_32470 v h) (hints_cons _ _ _ (der_32471 v h) (hints_cons _ _ _ (der_32472 v h) (hints_cons _ _ _ (der_32473 v h) (hints_cons _ _ _ (der_32474 v h) (hints_cons _ _ _ (der_32475 v h) (hints_cons _ _ _ (der_32476 v h) (hints_cons _ _ _ (der_32477 v h) (hints_cons _ _ _ (der_32478 v h) (hints_cons _ _ _ (der_32479 v h) (hints_cons _ _ _ (der_32480 v h) (hints_cons _ _ _ (der_32481 v h) (hints_cons _ _ _ (der_32482 v h) (hints_cons _ _ _ (der_32484 v h) (hints_cons _ _ _ (der_32485 v h) (hints_cons _ _ _ (der_32486 v h) (hints_cons _ _ _ (der_32487 v h) (hints_cons _ _ _ (der_32488 v h) (hints_cons _ _ _ (der_32489 v h) (hints_cons _ _ _ (der_32490 v h) (hints_cons _ _ _ (der_32491 v h) (hints_cons _ _ _ (der_32492 v h) (hints_cons _ _ _ (der_32494 v h) (hints_cons _ _ _ (der_32495 v h) (hints_cons _ _ _ (der_32496 v h) (hints_cons _ _ _ (der_32498 v h) (hints_cons _ _ _ (der_32499 v h) (hints_cons _ _ _ (der_32500 v h) (hints_cons _ _ _ (der_32501 v h) (hints_cons _ _ _ (der_32502 v h) (hints_cons _ _ _ (der_32504 v h) (hints_cons _ _ _ (der_32505 v h) (hints_cons _ _ _ (der_32507 v h) (hints_cons _ _ _ (der_32508 v h) (hints_cons _ _ _ (der_32509 v h) (hints_cons _ _ _ (der_32510 v h) (hints_cons _ _ _ (der_32511 v h) (hints_cons _ _ _ (der_32512 v h) (hints_cons _ _ _ (der_32513 v h) (hints_cons _ _ _ (der_32514 v h) (hints_cons _ _ _ (der_32515 v h) (hints_cons _ _ _ (der_32516 v h) (hints_cons _ _ _ (der_32517 v h) (hints_cons _ _ _ (der_32518 v h) (hints_cons _ _ _ (der_32519 v h) (hints_cons _ _ _ (der_32520 v h) (hints_cons _ _ _ (der_32521 v h) (hints_cons _ _ _ (der_32522 v h) (hints_cons _ _ _ (der_32523 v h) (hints_cons _ _ _ (der_32524 v h) (hints_cons _ _ _ (der_32526 v h) (hints_cons _ _ _ (der_32527 v h) (hints_cons _ _ _ (der_32528 v h) (hints_cons _ _ _ (der_32529 v h) (hints_cons _ _ _ (der_32530 v h) (hints_cons _ _ _ (der_32531 v h) (hints_cons _ _ _ (der_32532 v h) (hints_cons _ _ _ (der_32533 v h) (hints_cons _ _ _ (der_32535 v h) (hints_cons _ _ _ (der_32536 v h) (hints_cons _ _ _ (der_32537 v h) (hints_cons _ _ _ (der_32538 v h) (hints_cons _ _ _ (der_32539 v h) (hints_cons _ _ _ (der_32540 v h) (hints_cons _ _ _ (der_32541 v h) (hints_cons _ _ _ (der_32542 v h) (hints_cons _ _ _ (der_32543 v h) (hints_cons _ _ _ (der_32544 v h) (hints_cons _ _ _ (der_32545 v h) (hints_cons _ _ _ (der_32547 v h) (hints_cons _ _ _ (der_32548 v h) (hints_cons _ _ _ (der_32549 v h) (hints_cons _ _ _ (der_32550 v h) (hints_cons _ _ _ (der_32551 v h) (hints_cons _ _ _ (der_32552 v h) (hints_cons _ _ _ (der_32553 v h) (hints_cons _ _ _ (der_32555 v h) (hints_cons _ _ _ (der_32556 v h) (hints_cons _ _ _ (der_32557 v h) (hints_cons _ _ _ (der_32558 v h) (hints_cons _ _ _ (der_32559 v h) (hints_cons _ _ _ (der_32560 v h) (hints_cons _ _ _ (der_32561 v h) (hints_cons _ _ _ (der_32563 v h) (hints_cons _ _ _ (der_32564 v h) (hints_cons _ _ _ (der_32565 v h) (hints_cons _ _ _ (der_32567 v h) (hints_cons _ _ _ (der_32568 v h) (hints_cons _ _ _ (der_32569 v h) (hints_cons _ _ _ (der_32571 v h) (hints_cons _ _ _ (der_32572 v h) (hints_cons _ _ _ (der_32574 v h) (hints_cons _ _ _ (der_32575 v h) (hints_cons _ _ _ (der_32576 v h) (hints_cons _ _ _ (der_32577 v h) (hints_cons _ _ _ (der_32578 v h) (hints_cons _ _ _ (der_32579 v h) (hints_cons _ _ _ (der_32580 v h) (hints_cons _ _ _ (der_32581 v h) (hints_cons _ _ _ (der_32582 v h) (hints_cons _ _ _ (der_32583 v h) (hints_cons _ _ _ (der_32584 v h) (hints_cons _ _ _ (der_32585 v h) (hints_cons _ _ _ (der_32586 v h) (hints_cons _ _ _ (der_32587 v h) (hints_cons _ _ _ (der_32588 v h) (hints_cons _ _ _ (der_32589 v h) (hints_cons _ _ _ (der_32591 v h) (hints_cons _ _ _ (der_32592 v h) (hints_cons _ _ _ (der_32593 v h) (hints_cons _ _ _ (der_32594 v h) (hints_cons _ _ _ (der_32595 v h) (hints_cons _ _ _ (der_32596 v h) (hints_cons _ _ _ (der_32597 v h) (hints_cons _ _ _ (der_32598 v h) (hints_cons _ _ _ (der_32599 v h) (hints_cons _ _ _ (der_32600 v h) (hints_cons _ _ _ (der_32601 v h) (hints_cons _ _ _ (der_32602 v h) (hints_cons _ _ _ (der_32603 v h) (hints_cons _ _ _ (der_32604 v h) (hints_cons _ _ _ (der_32605 v h) (hints_cons _ _ _ (der_32606 v h) (hints_cons _ _ _ (der_32607 v h) (hints_cons _ _ _ (der_32608 v h) (hints_cons _ _ _ (der_32609 v h) (hints_cons _ _ _ (der_32610 v h) (hints_cons _ _ _ (der_32612 v h) (hints_cons _ _ _ (der_32613 v h) (hints_cons _ _ _ (der_32614 v h) (hints_cons _ _ _ (der_32615 v h) (hints_cons _ _ _ (der_32616 v h) (hints_cons _ _ _ (der_32617 v h) (hints_cons _ _ _ (der_32618 v h) (hints_cons _ _ _ (der_32619 v h) (hints_cons _ _ _ (der_32620 v h) (hints_cons _ _ _ (der_32621 v h) (hints_cons _ _ _ (der_32622 v h) (hints_cons _ _ _ (der_32624 v h) (hints_cons _ _ _ (der_32626 v h) (hints_cons _ _ _ (der_32628 v h) (hints_cons _ _ _ (der_32629 v h) (hints_cons _ _ _ (der_32631 v h) (hints_cons _ _ _ (der_32632 v h) (hints_cons _ _ _ (der_32633 v h) (hints_cons _ _ _ (der_32634 v h) (hints_cons _ _ _ (der_32636 v h) (hints_cons _ _ _ (der_32637 v h) (hints_cons _ _ _ (der_32638 v h) (hints_cons _ _ _ (der_32639 v h) (hints_cons _ _ _ (der_32640 v h) (hints_cons _ _ _ (der_32641 v h) (hints_cons _ _ _ (der_32642 v h) (hints_cons _ _ _ (der_32643 v h) (hints_cons _ _ _ (der_32644 v h) (hints_cons _ _ _ (der_32645 v h) (hints_cons _ _ _ (der_32646 v h) (hints_cons _ _ _ (der_32647 v h) (hints_cons _ _ _ (der_32649 v h) (hints_cons _ _ _ (der_32650 v h) (hints_cons _ _ _ (der_32651 v h) (hints_cons _ _ _ (der_32653 v h) (hints_cons _ _ _ (der_32654 v h) (hints_cons _ _ _ (der_32655 v h) (hints_cons _ _ _ (der_32656 v h) (hints_cons _ _ _ (der_32657 v h) (hints_cons _ _ _ (der_32658 v h) (hints_cons _ _ _ (der_32659 v h) (hints_cons _ _ _ (der_32660 v h) (hints_cons _ _ _ (der_32661 v h) (hints_cons _ _ _ (der_32662 v h) (hints_cons _ _ _ (der_32663 v h) (hints_cons _ _ _ (der_32664 v h) (hints_cons _ _ _ (der_32665 v h) (hints_cons _ _ _ (der_32666 v h) (hints_cons _ _ _ (der_32667 v h) (hints_cons _ _ _ (der_32668 v h) (hints_cons _ _ _ (der_32669 v h) (hints_cons _ _ _ (der_32670 v h) (hints_cons _ _ _ (der_32671 v h) (hints_cons _ _ _ (der_32672 v h) (hints_cons _ _ _ (der_32673 v h) (hints_cons _ _ _ (der_32674 v h) (hints_cons _ _ _ (der_32675 v h) (hints_cons _ _ _ (der_32676 v h) (hints_cons _ _ _ (der_32677 v h) (hints_cons _ _ _ (der_32678 v h) (hints_cons _ _ _ (der_32679 v h) (hints_cons _ _ _ (der_32680 v h) (hints_cons _ _ _ (der_32681 v h) (hints_cons _ _ _ (der_32682 v h) (hints_cons _ _ _ (der_32683 v h) (hints_cons _ _ _ (der_32684 v h) (hints_cons _ _ _ (der_32685 v h) (hints_cons _ _ _ (der_32686 v h) (hints_cons _ _ _ (der_32687 v h) (hints_cons _ _ _ (der_32688 v h) (hints_cons _ _ _ (der_32689 v h) (hints_cons _ _ _ (der_32690 v h) (hints_cons _ _ _ (der_32691 v h) (hints_cons _ _ _ (der_32692 v h) (hints_cons _ _ _ (der_32693 v h) (hints_cons _ _ _ (der_32694 v h) (hints_cons _ _ _ (der_32695 v h) (hints_cons _ _ _ (der_32696 v h) (hints_cons _ _ _ (der_32697 v h) (hints_cons _ _ _ (der_32698 v h) (hints_cons _ _ _ (der_32699 v h) (hints_cons _ _ _ (der_32700 v h) (hints_cons _ _ _ (der_32701 v h) (hints_cons _ _ _ (der_32702 v h) (hints_cons _ _ _ (der_32703 v h) (hints_cons _ _ _ (der_32704 v h) (hints_cons _ _ _ (der_32705 v h) (hints_cons _ _ _ (der_32706 v h) (hints_cons _ _ _ (der_32707 v h) (hints_cons _ _ _ (der_32709 v h) (hints_cons _ _ _ (der_32710 v h) (hints_cons _ _ _ (der_32711 v h) (hints_cons _ _ _ (der_32713 v h) (hints_cons _ _ _ (der_32714 v h) (hints_cons _ _ _ (der_32715 v h) (hints_cons _ _ _ (der_32717 v h) (hints_cons _ _ _ (der_32719 v h) (hints_cons _ _ _ (der_32721 v h) (hints_cons _ _ _ (der_32722 v h) (hints_cons _ _ _ (der_32723 v h) (hints_cons _ _ _ (der_32724 v h) (hints_cons _ _ _ (der_32725 v h) (hints_cons _ _ _ (der_32727 v h) (hints_cons _ _ _ (der_32728 v h) (hints_cons _ _ _ (der_32730 v h) (hints_cons _ _ _ (der_32731 v h) (hints_cons _ _ _ (der_32732 v h) (hints_cons _ _ _ (der_32733 v h) (hints_cons _ _ _ (der_32734 v h) (hints_cons _ _ _ (der_32735 v h) (hints_cons _ _ _ (der_32736 v h) (hints_cons _ _ _ (der_32737 v h) (hints_cons _ _ _ (der_32738 v h) (hints_cons _ _ _ (der_32740 v h) (hints_cons _ _ _ (der_32741 v h) (hints_cons _ _ _ (der_32742 v h) (hints_cons _ _ _ (der_32743 v h) (hints_cons _ _ _ (der_32744 v h) (hints_cons _ _ _ (der_32745 v h) (hints_cons _ _ _ (der_32746 v h) (hints_cons _ _ _ (der_32748 v h) (hints_cons _ _ _ (der_32749 v h) (hints_cons _ _ _ (der_32750 v h) (hints_cons _ _ _ (der_32751 v h) (hints_cons _ _ _ (der_32752 v h) (hints_cons _ _ _ (der_32753 v h) (hints_cons _ _ _ (der_32754 v h) (hints_cons _ _ _ (der_32755 v h) (hints_cons _ _ _ (der_32756 v h) (hints_cons _ _ _ (der_32757 v h) (hints_cons _ _ _ (der_32759 v h) (hints_cons _ _ _ (der_32760 v h) (hints_cons _ _ _ (der_32761 v h) (hints_cons _ _ _ (der_32763 v h) (hints_cons _ _ _ (der_32764 v h) (hints_cons _ _ _ (der_32765 v h) (hints_cons _ _ _ (der_32766 v h) (hints_cons _ _ _ (der_32767 v h) (hints_cons _ _ _ (der_32768 v h) (hints_cons _ _ _ (der_32769 v h) (hints_cons _ _ _ (der_32770 v h) (hints_cons _ _ _ (der_32772 v h) (hints_cons _ _ _ (der_32773 v h) (hints_cons _ _ _ (der_32774 v h) (hints_cons _ _ _ (der_32775 v h) (hints_cons _ _ _ (der_32776 v h) (hints_cons _ _ _ (der_32778 v h) (hints_cons _ _ _ (der_32779 v h) (hints_cons _ _ _ (der_32780 v h) (hints_cons _ _ _ (der_32781 v h) (hints_cons _ _ _ (der_32783 v h) (hints_cons _ _ _ (der_32784 v h) (hints_cons _ _ _ (der_32785 v h) (hints_cons _ _ _ (der_32786 v h) (hints_cons _ _ _ (der_32788 v h) (hints_cons _ _ _ (der_32789 v h) (hints_cons _ _ _ (der_32790 v h) (hints_cons _ _ _ (der_32792 v h) (hints_cons _ _ _ (der_32793 v h) (hints_cons _ _ _ (der_32794 v h) (hints_cons _ _ _ (der_32795 v h) (hints_cons _ _ _ (der_32796 v h) (hints_cons _ _ _ (der_32797 v h) (hints_cons _ _ _ (der_32798 v h) (hints_cons _ _ _ (der_32799 v h) (hints_cons _ _ _ (der_32800 v h) (hints_cons _ _ _ (der_32801 v h) (hints_cons _ _ _ (der_32802 v h) (hints_cons _ _ _ (der_32804 v h) (hints_cons _ _ _ (der_32805 v h) (hints_cons _ _ _ (der_32807 v h) (hints_cons _ _ _ (der_32809 v h) (hints_cons _ _ _ (der_32811 v h) (hints_cons _ _ _ (der_32812 v h) (hints_cons _ _ _ (der_32813 v h) (hints_cons _ _ _ (der_32814 v h) (hints_cons _ _ _ (der_32815 v h) (hints_cons _ _ _ (der_32816 v h) (hints_cons _ _ _ (der_32817 v h) (hints_cons _ _ _ (der_32818 v h) (hints_cons _ _ _ (der_32819 v h) (hints_cons _ _ _ (der_32820 v h) (hints_cons _ _ _ (der_32821 v h) (hints_cons _ _ _ (der_32822 v h) (hints_cons _ _ _ (der_32823 v h) (hints_cons _ _ _ (der_32825 v h) (hints_cons _ _ _ (der_32828 v h) (hints_cons _ _ _ (der_32829 v h) (hints_cons _ _ _ (der_32830 v h) (hints_cons _ _ _ (der_32831 v h) (hints_cons _ _ _ (der_32832 v h) (hints_cons _ _ _ (der_32833 v h) (hints_cons _ _ _ (der_32834 v h) (hints_cons _ _ _ (der_32835 v h) (hints_cons _ _ _ (der_32836 v h) (hints_cons _ _ _ (der_32837 v h) (hints_cons _ _ _ (der_32838 v h) (hints_cons _ _ _ (der_32839 v h) (hints_cons _ _ _ (der_32840 v h) (hints_cons _ _ _ (der_32841 v h) (hints_cons _ _ _ (der_32842 v h) (hints_cons _ _ _ (der_32843 v h) (hints_cons _ _ _ (der_32844 v h) (hints_cons _ _ _ (der_32845 v h) (hints_cons _ _ _ (der_32846 v h) (hints_cons _ _ _ (der_32847 v h) (hints_cons _ _ _ (der_32848 v h) (hints_cons _ _ _ (der_32849 v h) (hints_cons _ _ _ (der_32850 v h) (hints_cons _ _ _ (der_32851 v h) (hints_cons _ _ _ (der_32852 v h) (hints_cons _ _ _ (der_32853 v h) (hints_cons _ _ _ (der_32854 v h) (hints_cons _ _ _ (der_32855 v h) (hints_cons _ _ _ (der_32856 v h) (hints_cons _ _ _ (der_32857 v h) (hints_cons _ _ _ (der_32858 v h) (hints_cons _ _ _ (der_32859 v h) (hints_cons _ _ _ (der_32860 v h) (hints_cons _ _ _ (der_32861 v h) (by intro d hd; cases hd)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def prefix019 := prefix018 ++ chunk019
theorem prefix_sound019 (v : SatVar → Bool) (h : ∀ d ∈ normalizedCNF5, CNF.Holds v d) : ∀ c ∈ prefix019, CNF.Holds (v ∘ decodeVar) c := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact prefix_sound018 v h c hc
  · exact chunk_sound019 v h c hc
end Percolation.NReplay
