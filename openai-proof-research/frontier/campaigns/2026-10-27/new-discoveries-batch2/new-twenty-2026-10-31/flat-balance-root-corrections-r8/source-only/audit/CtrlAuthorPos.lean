/-
MathDB 352972 positive proof controls over the generic bridges.

TEN positive proof examples: every example below is a compiling proof of a
meaningful statement about the generic bridge layer or the concrete witness.
None is a failed-compilation test. Sensitivity/nonvacuity of the endpoint is
exercised by the parity, cutoff, cast, and bound-equivalence shapes.

M1 metadata note: the contrapositive control (C9) is proved from the
discrepancy hypothesis alone; its proof does not use any flatness hypothesis
(the binder is explicitly named and ignored), and no claim is made that it
uses `Flat`.

Pins: Lean v4.34.1, mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
-/

import FlatBalanceBridges

namespace FlatBalance

/-- C1. Generic empty-clique shape: for every finite simple graph whatever,
the 0-cliques are exactly the singleton empty vertex set. -/
example {V : Type} [Fintype V] (G : SimpleGraph V) : cliqueFinset G 0 = {∅} :=
  cliqueFinset_zero G

/-- C2. Generic `c_0 = 1`: every finite simple graph, the empty graph
included, has exactly one 0-clique. -/
example {V : Type} [Fintype V] (G : SimpleGraph V) : cliqueCount G 0 = 1 :=
  cliqueCount_zero G

/-- C3a. The convention is live on the witness: `c_0(K_{3,3}) = 1`. -/
example : cliqueCount K33 0 = 1 :=
  cliqueCount_zero (V := Fin 3 ⊕ Fin 3) K33

/-- C3b. The empty graph instance: the generic `c_0 = 1` applies to the
zero-vertex graph, where all higher counts vanish. -/
example : cliqueCount
    (⟨fun _ _ => False, fun _ _ h => h, fun _ h => h⟩ : SimpleGraph (Fin 0)) 0 = 1 :=
  cliqueCount_zero _



/-- C4. Generic finite support: no 7-cliques in any graph on six vertices
(the witness has exactly six). -/
example : cliqueCount K33 7 = 0 :=
  cliqueCount_of_card_lt K33 (show Fintype.card (Fin 3 ⊕ Fin 3) < 7 by decide)

/-- C5. Cutoff independence, instance: the odd selector sum over any range
beyond the vertex count is the intrinsic `oddCliqueSum`. -/
example : ∑ d ∈ Finset.range 9, (if d % 2 = 1 then cliqueCount K33 d else 0)
    = oddCliqueSum K33 :=
  oddCliqueSum_cutoff K33 (show Fintype.card (Fin 3 ⊕ Fin 3) < 9 by decide)

/-- C6. Cutoff independence, instance, even selector with `c_0` included. -/
example : ∑ d ∈ Finset.range 9, (if d % 2 = 0 then cliqueCount K33 d else 0)
    = evenCliqueSum K33 :=
  evenCliqueSum_cutoff K33 (show Fintype.card (Fin 3 ⊕ Fin 3) < 9 by decide)

/-- C7. Convention separation, instance: the `c_0`-inclusive even sum is the
positive-index even sum plus exactly `c_0 = 1`; the two conventions remain
distinct objects. -/
example : evenCliqueSum K33 = cliqueCount K33 0 + evenCliqueSumPos K33 :=
  evenCliqueSum_decomp K33

/-- C8. Integer cast bridge: `Int.natAbs` is the true absolute value in `Z`
(no truncated subtraction anywhere in the cast chain). -/
example (a b : ℕ) : (Int.natAbs ((a : ℤ) - (b : ℤ)) : ℤ) = |(a : ℤ) - (b : ℤ)| :=
  natAbs_cast_abs _

/-- C9. Generic contrapositive bridge, instance: a graph whose discrepancy
strictly exceeds one is not balanced. The proof uses only the discrepancy
hypothesis; no flatness hypothesis is consumed (the `_hf`-shaped binder is
absent here by construction, and none is claimed). -/
example (h : 1 < discrepancyNat K33) : ¬ Balanced K33 :=
  not_balanced_of_one_lt_discrepancy (V := Fin 3 ⊕ Fin 3) (G := K33) h

/-- C10. Real bound equivalence, instance: `Balanced` agrees with the
absolute-value bound over `R`, so the endpoint hypothesis transfers through
the cast bridge without reproof. -/
example : Balanced K33
    ↔ |(Nat.cast (oddCliqueSum K33) : ℝ) - (Nat.cast (evenCliqueSum K33) : ℝ)| ≤ 1 :=
  balanced_iff_absReal K33

end FlatBalance
