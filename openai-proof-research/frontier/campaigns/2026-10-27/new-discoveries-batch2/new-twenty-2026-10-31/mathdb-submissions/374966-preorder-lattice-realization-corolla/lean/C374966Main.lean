import C374966Transmute
import C374966Lattice

/-!
# MathDB 374966 — literal refutation endpoint

Conjecture 8.1 of Athanasiadis–Chapoton (arXiv:2605.26916v1): for every preorder `τ` of size `n`
there is a finite graded lattice `L_τ` of rank `n` with `Z(P_τ,t) = Z(L_τ,t)` and
`M̄_{P_τ}(x,y) = M_{L_τ}(x,y)`.  For the corolla `τ = t₃` (`n = 3`) no finite graded lattice of
rank 3 satisfies even the M-equality, so the zeta conjunct is redundant.
-/

namespace C374966

open Finset MvPolynomial

universe u

/-- Lattice points of `Q_τ` for an arbitrary preorder relation `le` on `Fin n` (source §1, (2)). -/
def QPre {n : ℕ} (le : Fin n → Fin n → Prop) (v : Fin n → ℤ) : Prop :=
  (∀ e, 0 ≤ v e) ∧
    ∀ I : Finset (Fin n), (∀ b ∈ I, ∀ a, le a b → a ∈ I) → ∑ e ∈ I, v e ≤ (I.card : ℤ)

/-- The corolla domain is the general preorder-polytope domain at `τ = cor`. -/
theorem Qcor_eq_QPre : Qcor = QPre cor := rfl

/-- No finite graded lattice of rank 3 has `M_L = M̄_{P_τ}` for the corolla `τ = t₃`. -/
theorem corolla_no_M_match (L : Type u) [Lattice L] [BoundedOrder L] [Fintype L]
    [DecidableEq L] [DecidableLE L] [LocallyFiniteOrder L] (ρ : L → ℕ)
    (hg : IsGradedRank ρ 3) :
    transmute (Mtri P rk) ≠ algebraMap Pxy FracXY (Mtri L ρ) := by
  intro h
  rw [transmute_MP] at h
  have h2 : tab tMq = Mtri L ρ := iota_injective h
  obtain ⟨-, c11, c22, -, c12⟩ := Mbar_coeffs
  rw [h2] at c11 c22 c12
  exact no_lattice_core ρ hg.strictMono c11 c22 c12

/-- **Literal endpoint.** Conjecture 8.1 fails at the corolla `τ = t₃` (`n = 3`). -/
theorem conj81_false_at_corolla :
    ¬ ∃ (L : Type u) (_ : Lattice L) (_ : BoundedOrder L) (_ : Fintype L) (_ : DecidableEq L)
      (_ : DecidableLE L) (_ : LocallyFiniteOrder L) (ρ : L → ℕ),
      IsGradedRank ρ 3 ∧ transmute (Mtri P rk) = algebraMap Pxy FracXY (Mtri L ρ) := by
  rintro ⟨L, _, _, _, _, _, _, ρ, hg, h⟩
  exact corolla_no_M_match L ρ hg h

/-- **Literal endpoint with the zeta conjunct.** For any predicate `Zeta` standing for
`Z(P_τ,t) = Z(L,t)` on the same lattice, the full conjunction of Conjecture 8.1 fails. -/
theorem conj81_false_at_corolla_with_zeta
    (Zeta : ∀ (L : Type u) [Lattice L] [Fintype L], Prop) :
    ¬ ∃ (L : Type u) (_ : Lattice L) (_ : BoundedOrder L) (_ : Fintype L) (_ : DecidableEq L)
      (_ : DecidableLE L) (_ : LocallyFiniteOrder L) (ρ : L → ℕ),
      IsGradedRank ρ 3 ∧ Zeta L ∧ transmute (Mtri P rk) = algebraMap Pxy FracXY (Mtri L ρ) := by
  rintro ⟨L, _, _, _, _, _, _, ρ, hg, -, h⟩
  exact corolla_no_M_match L ρ hg h

/-- The same endpoint for Mathlib's standard graded orders `GradeOrder ℕ L`. -/
theorem conj81_false_at_corolla_gradeOrder (L : Type u) [Lattice L] [BoundedOrder L]
    [Fintype L] [DecidableEq L] [DecidableLE L] [LocallyFiniteOrder L] [GradeOrder ℕ L]
    (hb : grade ℕ (⊥ : L) = 0) (ht : grade ℕ (⊤ : L) = 3) :
    transmute (Mtri P rk) ≠ algebraMap Pxy FracXY (Mtri L (grade ℕ)) :=
  corolla_no_M_match L (grade ℕ) (isGradedRank_of_gradeOrder hb ht)

#print axioms conj81_false_at_corolla
#print axioms conj81_false_at_corolla_with_zeta
#print axioms conj81_false_at_corolla_gradeOrder
#print axioms corolla_no_M_match
#print axioms Qcor_eq_QPre
#print axioms ideals_iff
#print axioms Qcor_iff
#print axioms mem_pts
#print axioms card_P
#print axioms le_iff
#print axioms intervalIso
#print axioms rk_strictMono
#print axioms rk_covBy
#print axioms rk_of_maximal
#print axioms botP_le
#print axioms mu_eq_of_sum
#print axioms mu_P
#print axioms Tz_table
#print axioms Mtri_P_lit
#print axioms one_sub_xy_ne
#print axioms iota_injective
#print axioms transmute_MP_lit
#print axioms transmute_MP
#print axioms Mbar_coeffs
#print axioms isGradedRank_of_gradeOrder
#print axioms rank_one_iff_bot_covBy
#print axioms covBy_of_rank
#print axioms mu_cover
#print axioms Tab_diag
#print axioms Tab_cover
#print axioms join_eq
#print axioms count_bound
#print axioms two_mul_le_choose_two_add_three
#print axioms no_lattice_core

end C374966
