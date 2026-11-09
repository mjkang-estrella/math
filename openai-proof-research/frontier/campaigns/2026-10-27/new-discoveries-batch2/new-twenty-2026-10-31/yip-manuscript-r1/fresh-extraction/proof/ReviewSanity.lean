/-
  REVIEWER SUPPLEMENT (not part of the literal mathematical module).
  Prints the literal definitions and re-states the two endpoints and key
  intermediate facts with their intended types, so a reader can compare them
  with the source conjecture.  Nothing here is used by the endpoints.
-/
import Yip355956
set_option warningAsError true
open MathDB355956
#print dPowers
#print GPAdj
#print IsGPClique
#print IsMaximalGPClique
#print subfieldSet
#print admissibleR
#print YipConjecture
#print GPGraph
#print YipConjectureSG
#print wit
#print fK
-- the endpoints have exactly the negated conjecture types
example : ¬ YipConjecture := yip_conjecture_false
example : ¬ YipConjectureSG := yip_conjecture_SG_false
-- the only admissible r for (p, m, d) = (5, 8, 3) is 1
example : IsGreatest (admissibleR 5 8 3) 1 := admissibleR_greatest
-- the hypotheses instantiated by the endpoint are satisfiable (non-vacuity)
example : (5 : ℕ) ^ 8 ≡ 1 [MOD 2 * 3] := by decide
example : (5 : ℕ) ^ 8 = 390625 := by norm_num
instance sanityFact5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
example : Nat.card (GaloisField 5 8) = 5 ^ 8 := GaloisField.card 5 8 (by norm_num)
-- the main finite-field statement, for every field with 5^8 elements
example {K : Type} [Field K] [Finite K] (hK : Nat.card K = 5 ^ 8) :
    IsGPClique K 3 (subfieldSet K 5) ∧ ¬ IsMaximalGPClique K 3 (subfieldSet K 5) :=
  not_maximal_of_card hK
-- subfieldSet K 5 is exactly {0,1,2,3,4} in characteristic 5
example {K : Type} [Field K] (h5 : (5 : K) = 0) (z : K) :
    z ∈ subfieldSet K 5 ↔ z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 ∨ z = 4 := mem_subfieldSet_iff h5 z
-- GPGraph adjacency is the symmetrised literal relation (definitional unfolding)
example {K : Type} [Field K] (u v : K) :
    (GPGraph K 3).Adj u v ↔ u ≠ v ∧ (GPAdj K 3 u v ∨ GPAdj K 3 v u) := Iff.rfl
#print axioms yip_conjecture_false
#print axioms yip_conjecture_SG_false
