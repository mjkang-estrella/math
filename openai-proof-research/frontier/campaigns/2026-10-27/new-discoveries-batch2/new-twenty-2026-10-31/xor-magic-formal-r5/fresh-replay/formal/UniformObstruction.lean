import GeneralObstruction
import BaseEndpoints
/-! Review positive controls: the uniform literal negation and a connectivity-free
obstruction are short corollaries of the packet; these are reviewer checks, not
packet content. -/
namespace XorMagicFinal
open XorMagic

theorem not_printed_uniform (n : ℕ) (hn : 3 ≤ n) : ¬ PrintedAt n := by
  intro h
  have h8 : 8 ≤ 2^n :=
    calc 8 = 2^3 := by norm_num
      _ ≤ 2^n := Nat.pow_le_pow_right (by norm_num) hn
  have hpow : 2^n = 2 * 2^(n-1) := by
    rw [← pow_succ']; congr 1; omega
  apply not_closed_top_four (n := n) (by omega)
  exact h.2 (2^n-4) ⟨2^(n-1) - 2, by omega⟩ (by omega) le_rfl

theorem not_printed_ge_four_uniform : ∀ n, 4 ≤ n → ¬ PrintedAt n :=
  fun n hn => not_printed_uniform n (by omega)

/-- The obstruction does not need connectivity of G (relevant if MathDB's
"graph" is read without the source's connectedness requirement). -/
theorem no_closed_top_four_any {V : Type} [Fintype V] [DecidableEq V] {n : ℕ} (hn : 2 ≤ n)
    (G : SimpleGraph V) [DecidableRel G.Adj] (reg : G.IsRegularOfDegree (2^n-4))
    (l : V ≃ Bits n) (hl : ∀ v, l v + ∑ u ∈ G.neighborFinset v, l u = 0) : False := by
  classical
  have hc := card_of_label l
  have power : 4 ≤ 2^n :=
    calc 4 = 2^2 := by decide
      _ ≤ 2^n := Nat.pow_le_pow_right (by decide) hn
  have hr : Gᶜ.IsRegularOfDegree 3 := by
    have hh := reg.compl
    have degree : Fintype.card V-1-(2^n-4) = 3 := by omega
    simpa only [degree] using hh
  apply cubic_obstruction Gᶜ hr l
  intro v
  rw [complement_identity G l (total_labels hn l) v]
  exact hl v

/-- Bases give the corrected statement at n = 4, 5 together with the literal negation. -/
theorem base_summary : CorrectedAt 4 ∧ CorrectedAt 5 ∧ ¬ PrintedAt 4 ∧ ¬ PrintedAt 5 :=
  ⟨corrected_at_4, corrected_at_5, not_printed_uniform 4 (by norm_num), not_printed_uniform 5 (by norm_num)⟩
end XorMagicFinal
#print axioms XorMagicFinal.not_printed_ge_four_uniform
#print axioms XorMagicFinal.no_closed_top_four_any
#print axioms XorMagicFinal.base_summary
