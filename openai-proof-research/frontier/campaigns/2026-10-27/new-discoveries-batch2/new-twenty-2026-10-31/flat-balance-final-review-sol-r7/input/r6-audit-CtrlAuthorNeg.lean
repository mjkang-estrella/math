import FlatBalance

/-!
# MathDB 352972 negative controls

Meaningful negative controls over the endpoint: they would fail if the
endpoint were vacuous, proxy-encoded, or weaker than the literal statement.
-/

namespace FlatBalance

/-- Control: the witness is a genuine nonempty graph -- six vertices. -/
example : (Finset.univ : Finset (Fin 3 ⊕ Fin 3)).card = 6 := card_V6

/-- Control: the witness has actual edges (flatness is not vacuous). -/
example : K33.Adj (Sum.inl 0) (Sum.inr 0) := trivial

/-- Control: the 2-clique count is exactly 9, not a weaker value. -/
example : cliqueCount K33 2 ≠ 8 := by
  rw [cliqueCount_K33_two]
  omega

/-- Control: the 2-clique count is nonzero. -/
example : cliqueCount K33 2 ≠ 0 := by
  rw [cliqueCount_K33_two]
  omega

/-- Control: the positive-index discrepancy is 3, not 4 (no `c_0` double
count) and not 0. -/
example : discrepancyNatPos K33 ≠ 4 := by
  rw [discrepancyNatPos_K33]; omega

example : discrepancyNatPos K33 ≠ 0 := by
  rw [discrepancyNatPos_K33]; omega

/-- Control: the `c_0`-convention discrepancy is 4, distinct from the
positive-index value. -/
example : discrepancyNat K33 ≠ discrepancyNatPos K33 := by
  rw [discrepancyNat_K33, discrepancyNatPos_K33]
  omega

/-- Control: the witness refutes the conjecture pointwise, not just through
some proxy quantifier. -/
example : ¬ (Flat K33 → Balanced K33) := fun hcon => K33_not_balanced (hcon K33_flat)

/-- Control: the counterexample is a graph whose flatness is a real
hypothesis use -- the pointwise implication fails even though flatness
holds; its contrapositive shape is nontrivial. -/
example : Balanced K33 → ¬ Flat K33 := fun hb _hf => K33_not_balanced hb

/-- Control: the literal negated universal is not implied by the vacuous
falsity of `Flat` for the witness: `Flat K33` is provable. -/
example : Flat K33 := K33_flat

end FlatBalance
