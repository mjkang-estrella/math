import C374966Defs
import Mathlib.Order.Grade
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.IntervalCases

/-!
# MathDB 374966 — finite graded lattices cannot have the corolla M-triangle data

For a finite lattice with a strictly monotone rank map `ρ` (in particular any graded lattice):
`[x^k y^k] M_L = #{ρ = k}` and `[x y²] M_L = -∑_{ρ c = 2} d_c` with `d_c = #{a ≤ c, ρ a = 1}`.
Two distinct rank-1 elements below a rank-2 element `c` have join `c`, so
`∑ C(d_c, 2) ≤ C(#{ρ = 1}, 2)`. With counts `5, 5` and `∑ d_c = 13` this is impossible.
-/

namespace C374966

open Finset MvPolynomial

/-- A rank map making a bounded poset graded of rank `n`. -/
structure IsGradedRank {L : Type*} [PartialOrder L] [BoundedOrder L] (ρ : L → ℕ) (n : ℕ) :
    Prop where
  strictMono : StrictMono ρ
  covBy : ∀ a b : L, a ⋖ b → ρ b = ρ a + 1
  bot : ρ ⊥ = 0
  top : ρ ⊤ = n

/-- Binding to Mathlib's standard graded orders. -/
theorem isGradedRank_of_gradeOrder {L : Type*} [PartialOrder L] [BoundedOrder L]
    [GradeOrder ℕ L] {n : ℕ} (hb : grade ℕ (⊥ : L) = 0) (ht : grade ℕ (⊤ : L) = n) :
    IsGradedRank (grade ℕ : L → ℕ) n where
  strictMono := grade_strictMono (𝕆 := ℕ)
  covBy _ _ h := (Nat.covBy_iff_add_one_eq.1 (CovBy.grade (𝕆 := ℕ) h)).symm
  bot := hb
  top := ht

variable {L : Type*}

theorem eq_of_le_of_rank_ge [PartialOrder L] {ρ : L → ℕ} (hρ : StrictMono ρ) {u v : L}
    (h : u ≤ v) (hr : ρ v ≤ ρ u) : u = v := by
  by_contra hne
  have := hρ (lt_of_le_of_ne h hne)
  omega

/-- Comparable points of successive rank form a cover. -/
theorem covBy_of_rank [PartialOrder L] {ρ : L → ℕ} (hρ : StrictMono ρ) {a b : L}
    (hab : a ≤ b) (hr : ρ b = ρ a + 1) : a ⋖ b := by
  refine ⟨lt_of_le_of_ne hab ?_, ?_⟩
  · intro h
    rw [h] at hr
    omega
  · intro c hac hcb
    have h1 := hρ hac
    have h2 := hρ hcb
    omega

/-- In a graded poset the rank-one layer is exactly the set of atoms. -/
theorem rank_one_iff_bot_covBy [PartialOrder L] [BoundedOrder L] {ρ : L → ℕ} {n : ℕ}
    (hg : IsGradedRank ρ n) (a : L) : ρ a = 1 ↔ ⊥ ⋖ a := by
  constructor
  · intro h
    exact covBy_of_rank hg.strictMono bot_le (by have := hg.bot; omega)
  · intro h
    have h1 := hg.covBy _ _ h
    have h2 := hg.bot
    omega

/-- `μ = -1` on comparable pairs of ranks `1 < 2`. -/
theorem mu_cover [PartialOrder L] [LocallyFiniteOrder L] [DecidableEq L] {ρ : L → ℕ}
    (hρ : StrictMono ρ) {a b : L} (ha : ρ a = 1) (hb : ρ b = 2) (hab : a ≤ b) :
    IncidenceAlgebra.mu ℚ a b = -1 := by
  have hne : a ≠ b := by
    intro h
    rw [h] at ha
    omega
  rw [IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne hne]
  have hIco : Finset.Ico a b = {a} := by
    ext x
    rw [Finset.mem_Ico, Finset.mem_singleton]
    constructor
    · rintro ⟨hax, hxb⟩
      by_contra hxa
      have h1 := hρ (lt_of_le_of_ne hax (Ne.symm hxa))
      have h2 := hρ hxb
      omega
    · rintro rfl
      exact ⟨le_rfl, lt_of_le_of_ne hab hne⟩
  rw [hIco, Finset.sum_singleton, IncidenceAlgebra.mu_apply, ite_eq_left rfl]

/-- Diagonal coefficients count rank layers. -/
theorem Tab_diag [PartialOrder L] [Fintype L] [LocallyFiniteOrder L] [DecidableEq L]
    [DecidableLE L] {ρ : L → ℕ} (hρ : StrictMono ρ) (k : ℕ) :
    Tab L ρ k k = ((univ.filter (fun a => ρ a = k)).card : ℚ) := by
  unfold Tab
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : ρ a = k
  · rw [ite_eq_left ha, Nat.cast_one, Finset.sum_eq_single a]
    · rw [ite_eq_left (And.intro ha ha), ite_eq_left le_rfl, IncidenceAlgebra.mu_apply,
        ite_eq_left rfl]
    · intro b _ hb
      by_cases hb' : ρ a = k ∧ ρ b = k
      · rw [ite_eq_left hb', ite_eq_right]
        intro hab
        exact hb (eq_of_le_of_rank_ge hρ hab (le_of_eq (hb'.2.trans hb'.1.symm))).symm
      · rw [ite_eq_right hb']
    · intro h
      exact absurd (Finset.mem_univ a) h
  · rw [ite_eq_right ha, Nat.cast_zero]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [ite_eq_right (show ¬ (ρ a = k ∧ ρ b = k) from fun h => ha h.1)]

/-- The `x y²` coefficient is minus the number of rank-1/rank-2 covers. -/
theorem Tab_cover [PartialOrder L] [Fintype L] [LocallyFiniteOrder L] [DecidableEq L]
    [DecidableLE L] {ρ : L → ℕ} (hρ : StrictMono ρ) :
    Tab L ρ 1 2 = -∑ b ∈ univ.filter (fun b => ρ b = 2),
      ((univ.filter (fun a => ρ a = 1 ∧ a ≤ b)).card : ℚ) := by
  have hterm : ∀ a b : L,
      (if ρ a = 1 ∧ ρ b = 2 then (if a ≤ b then IncidenceAlgebra.mu ℚ a b else 0) else 0)
        = -(if ρ b = 2 then (if ρ a = 1 ∧ a ≤ b then (1 : ℚ) else 0) else 0) := by
    intro a b
    by_cases h1 : ρ a = 1 ∧ ρ b = 2
    · rw [ite_eq_left h1, ite_eq_left h1.2]
      by_cases h2 : a ≤ b
      · rw [ite_eq_left h2, ite_eq_left (And.intro h1.1 h2), mu_cover hρ h1.1 h1.2 h2]
      · rw [ite_eq_right h2, ite_eq_right (show ¬ (ρ a = 1 ∧ a ≤ b) from fun h => h2 h.2),
          neg_zero]
    · rw [ite_eq_right h1]
      by_cases hb : ρ b = 2
      · rw [ite_eq_left hb,
          ite_eq_right (show ¬ (ρ a = 1 ∧ a ≤ b) from fun h => h1 ⟨h.1, hb⟩), neg_zero]
      · rw [ite_eq_right hb, neg_zero]
  calc Tab L ρ 1 2
      = ∑ a, ∑ b, -(if ρ b = 2 then (if ρ a = 1 ∧ a ≤ b then (1 : ℚ) else 0) else 0) := by
        unfold Tab
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hterm a b
    _ = -∑ b, ∑ a, (if ρ b = 2 then (if ρ a = 1 ∧ a ≤ b then (1 : ℚ) else 0) else 0) := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_neg_distrib]
    _ = -∑ b, (if ρ b = 2 then ((univ.filter (fun a => ρ a = 1 ∧ a ≤ b)).card : ℚ) else 0) := by
        congr 1
        refine Finset.sum_congr rfl fun b _ => ?_
        by_cases hb : ρ b = 2
        · simp only [ite_eq_left hb]
          rw [Finset.sum_boole]
        · simp only [ite_eq_right hb, Finset.sum_const_zero]
    _ = -∑ b ∈ univ.filter (fun b => ρ b = 2),
          ((univ.filter (fun a => ρ a = 1 ∧ a ≤ b)).card : ℚ) := by
        rw [Finset.sum_filter]

/-- Two distinct rank-1 elements below a rank-2 element `b` have join `b`. -/
theorem join_eq [Lattice L] {ρ : L → ℕ} (hρ : StrictMono ρ) {x y b : L}
    (hx : ρ x = 1) (hy : ρ y = 1) (hxy : x ≠ y) (hxb : x ≤ b) (hyb : y ≤ b) (hb : ρ b = 2) :
    x ⊔ y = b := by
  have h1 : x < x ⊔ y := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro h
    have hyx : y ≤ x := by
      rw [h]
      exact le_sup_right
    exact hxy (eq_of_le_of_rank_ge hρ hyx (by omega)).symm
  have h2 := hρ h1
  exact eq_of_le_of_rank_ge hρ (sup_le hxb hyb) (by omega)

/-- Double counting of atom pairs under rank-2 elements. -/
theorem count_bound [Lattice L] [Fintype L] [DecidableEq L] [DecidableLE L]
    (ρ : L → ℕ) (hρ : StrictMono ρ) :
    ∑ b ∈ univ.filter (fun b => ρ b = 2), (univ.filter (fun a => ρ a = 1 ∧ a ≤ b)).card.choose 2
      ≤ (univ.filter (fun a => ρ a = 1)).card.choose 2 := by
  have hdisj : ((univ.filter (fun b => ρ b = 2) : Finset L) : Set L).PairwiseDisjoint
      (fun b => (univ.filter (fun a => ρ a = 1 ∧ a ≤ b)).powersetCard 2) := by
    intro b hb b' hb' hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro s hs hs'
    simp only [Finset.mem_powersetCard] at hs hs'
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 hs.2
    have hx := hs.1 (Finset.mem_insert_self x {y})
    have hy := hs.1 (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
    have hx' := hs'.1 (Finset.mem_insert_self x {y})
    have hy' := hs'.1 (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy hx' hy'
    have hb2 : ρ b = 2 := by simpa using hb
    have hb2' : ρ b' = 2 := by simpa using hb'
    apply hne
    rw [← join_eq hρ hx.1 hy.1 hxy hx.2 hy.2 hb2, join_eq hρ hx'.1 hy'.1 hxy hx'.2 hy'.2 hb2']
  calc ∑ b ∈ univ.filter (fun b => ρ b = 2),
          (univ.filter (fun a => ρ a = 1 ∧ a ≤ b)).card.choose 2
      = ∑ b ∈ univ.filter (fun b => ρ b = 2),
          ((univ.filter (fun a => ρ a = 1 ∧ a ≤ b)).powersetCard 2).card := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.card_powersetCard]
    _ = ((univ.filter (fun b => ρ b = 2)).biUnion
          (fun b => (univ.filter (fun a => ρ a = 1 ∧ a ≤ b)).powersetCard 2)).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ ((univ.filter (fun a => ρ a = 1)).powersetCard 2).card := by
        apply Finset.card_le_card
        intro s hs
        rw [Finset.mem_biUnion] at hs
        obtain ⟨b, _, hs⟩ := hs
        refine Finset.powersetCard_mono ?_ hs
        intro a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
        exact ha.1
    _ = (univ.filter (fun a => ρ a = 1)).card.choose 2 := Finset.card_powersetCard 2 _

/-- `C(d,2) + 3 ≥ 2d` for all `d` (equivalently `(d-2)(d-3) ≥ 0`). -/
theorem two_mul_le_choose_two_add_three (d : ℕ) : 2 * d ≤ d.choose 2 + 3 := by
  induction d with
  | zero => decide
  | succ n ih =>
    have e : (n + 1).choose 2 = n.choose 1 + n.choose 2 := Nat.choose_succ_succ' n 1
    rw [e, Nat.choose_one_right]
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> decide
    · omega

/-- Core obstruction: no finite lattice with a strictly monotone rank map has
`[xy]M = 5`, `[x²y²]M = 5` and `[xy²]M = -13`. -/
theorem no_lattice_core [Lattice L] [Fintype L] [LocallyFiniteOrder L] [DecidableEq L]
    [DecidableLE L] (ρ : L → ℕ) (hρ : StrictMono ρ)
    (h11 : (Mtri L ρ).coeff (mon 1 1) = 5) (h22 : (Mtri L ρ).coeff (mon 2 2) = 5)
    (h12 : (Mtri L ρ).coeff (mon 1 2) = -13) : False := by
  rw [coeff_Mtri, Tab_diag hρ] at h11
  rw [coeff_Mtri, Tab_diag hρ] at h22
  rw [coeff_Mtri, Tab_cover hρ] at h12
  have hA : (univ.filter (fun a => ρ a = 1)).card = 5 := by exact_mod_cast h11
  have hB : (univ.filter (fun a => ρ a = 2)).card = 5 := by exact_mod_cast h22
  have hE : ∑ b ∈ univ.filter (fun b => ρ b = 2),
      (univ.filter (fun a => ρ a = 1 ∧ a ≤ b)).card = 13 := by
    have h : ∑ b ∈ univ.filter (fun b => ρ b = 2),
        ((univ.filter (fun a => ρ a = 1 ∧ a ≤ b)).card : ℚ) = 13 := by
      linarith
    exact_mod_cast h
  have hcb := count_bound ρ hρ
  rw [hA] at hcb
  have hsum : ∑ b ∈ univ.filter (fun b => ρ b = 2),
        2 * (univ.filter (fun a => ρ a = 1 ∧ a ≤ b)).card
      ≤ ∑ b ∈ univ.filter (fun b => ρ b = 2),
        ((univ.filter (fun a => ρ a = 1 ∧ a ≤ b)).card.choose 2 + 3) :=
    Finset.sum_le_sum fun b _ => two_mul_le_choose_two_add_three _
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, hB, hE] at hsum
  have h10 : Nat.choose 5 2 = 10 := by decide
  omega

end C374966
