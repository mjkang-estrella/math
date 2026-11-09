import Std
set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace Percolation333709
-- Literal PG(2,5) incidence data. This file contains no claimed refutation endpoint.
def lines : List Nat := [2113929216,50872848,37884036,42213640,35719234,1106247680,537989392,135531012,269631560,68690050,1073773568,270795920,545784900,71370248,151127298,1074757632,138453072,69255428,553683080,276861442,1073742816,75630640,285286436,136843304,541343778,1073741855,539107841,142688385,273156353,84152385,34636833]
def members (a : Nat) : List Nat := (List.range 31).filter (fun p => a.testBit p)
def count (a : Nat) : Nat := (members a).length
def step (a : Nat) : Nat := lines.foldl (fun b l => if count (a &&& l) >= 5 then b ||| l else b) a
def iterate (a : Nat) : Nat -> Nat
 | 0 => a
 | n+1 => step (iterate a n)
def full : Nat := 2147483647
-- Source semantics over point predicates, with exact unbounded percolation quantifier.
abbrev Point := Fin 31
abbrev PointSet := Point -> Bool
def setCountOn (a : PointSet) (l : Nat) : Nat :=
 ((List.finRange 31).filter (fun p => a p && l.testBit p.val)).length
def sourceStep (a : PointSet) : PointSet := fun p =>
 a p || lines.any (fun l => l.testBit p.val && decide (setCountOn a l >= 5))
def sourceIter (a : PointSet) : Nat -> PointSet
 | 0 => a
 | n+1 => sourceStep (sourceIter a n)
def sourceFull (a : PointSet) : Prop := forall p, a p = true
def Percolates (a : PointSet) : Prop := exists n, sourceFull (sourceIter a n)
def Subset (a b : PointSet) : Prop := forall p, a p = true -> b p = true
def InclusionMinimal (a : PointSet) : Prop :=
 Percolates a /\ forall b, Subset b a -> b ≠ a -> Not (Percolates b)
def TwoRounds (a : PointSet) : Prop :=
 sourceFull (sourceIter a 2) /\ Not (sourceFull (sourceIter a 1))
def TargetNegationOnThisPlane : Prop := Not (exists a, InclusionMinimal a /\ TwoRounds a)
def planeCheck : Bool :=
 (decide (lines.length = 31)) &&
 lines.all (fun l => decide (count l = 6)) &&
 (List.range 31).all (fun p => decide ((lines.filter (fun l => l.testBit p)).length = 6)) &&
 lines.all (fun l => lines.all (fun k => l == k || decide (count (l &&& k) = 1))) &&
 (List.range 31).all (fun p => (List.range 31).all (fun q => p == q ||
   decide ((lines.filter (fun l => l.testBit p && l.testBit q)).length = 1))) &&
 lines.all (fun l => decide (([0,25,30,6].filter (fun p => l.testBit p)).length <= 2))
theorem plane_checks : planeCheck = true := by decide
-- A finite diagnostic certificate, deliberately not labeled a proof of the conjecture's negation.
def threeRoundWitness : Nat := 241579737
def deletionSeparators : List (Nat × Nat) := [(0,510113500),(3,2137437909),(4,795293389),(6,2120693407),(7,795326041),(9,526824669),(10,796310237),(12,2121246425),(13,526849757),(17,526759641),(18,778286813),(21,256358109),(22,2133210841),(25,1030209241),(26,979810013),(27,929511165)]
def witnessCheck : Bool :=
 decide (iterate threeRoundWitness 2 != full) && decide (iterate threeRoundWitness 3 = full) &&
 (members threeRoundWitness).all (fun v => deletionSeparators.any (fun vb =>
  decide (vb.1 = v) && !(vb.2.testBit v) &&
  decide (((threeRoundWitness ^^^ (1 <<< v)) &&& vb.2) = (threeRoundWitness ^^^ (1 <<< v))) &&
  decide (step vb.2 = vb.2)))
theorem three_round_diagnostic : witnessCheck = true := by decide
#print axioms plane_checks
#print axioms three_round_diagnostic
end Percolation333709
