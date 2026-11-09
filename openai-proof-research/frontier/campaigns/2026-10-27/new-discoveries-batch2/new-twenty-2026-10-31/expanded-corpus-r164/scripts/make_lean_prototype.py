import pathlib,json,random
D=pathlib.Path(__file__).resolve().parents[1];d=next(x for x in json.loads((D/'outputs/percolation.json').read_text()) if x['q']==5);L=d['lines'];N=31;full=(1<<31)-1;rng=random.Random(164709)
def step(a):
 b=a
 for l in L:
  if (a&l).bit_count()>=5:b|=l
 return b
def close(a):
 while 1:
  b=step(a)
  if b==a:return a
  a=b
for trial in range(2000):
 a=full;o=list(range(31));rng.shuffle(o)
 for v in o:
  b=a&~(1<<v)
  if close(b)==full:a=b
 if step(step(a))!=full and step(step(step(a)))==full:break
else:raise Exception('no 3-round witness')
rec={'mask':a,'rounds':[a,step(a),step(step(a)),full],'deletion_closures':{str(v):close(a&~(1<<v)) for v in range(31) if a>>v&1}}
(D/'outputs/percolation-three-round.json').write_text(json.dumps(rec,indent=2))
s='''import Std
set_option maxRecDepth 20000
set_option maxHeartbeats 0
namespace Percolation333709
-- Literal PG(2,5) incidence data. This file contains no claimed refutation endpoint.
def lines : List Nat := [%s]
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
 Percolates a /\ forall b, Subset b a -> b != a -> Not (Percolates b)
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
def threeRoundWitness : Nat := %d
def witnessCheck : Bool :=
 decide (iterate threeRoundWitness 2 != full) && decide (iterate threeRoundWitness 3 = full) &&
 (members threeRoundWitness).all (fun v =>
  let b := iterate (threeRoundWitness ^^^ (1 <<< v)) 31
  decide (b != full) && decide (step b = b))
theorem three_round_diagnostic : witnessCheck = true := by decide
#print axioms plane_checks
#print axioms three_round_diagnostic
end Percolation333709
'''%(','.join(map(str,L)),a)
(D/'lean/PlaneData.lean').write_text(s)
print(rec)
