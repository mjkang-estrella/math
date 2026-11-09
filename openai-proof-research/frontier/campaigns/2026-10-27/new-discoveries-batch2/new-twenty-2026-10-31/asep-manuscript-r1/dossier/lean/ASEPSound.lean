import ASEPDefs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A sufficient condition for non-adjacency

Let `x ∈ P_ASEP^8` have entries in `{0} ∪ [1/4, ∞)` and cut values in `{1} ∪ [5/4, ∞)`, let `T` be the
0/1 matrix of a map `σ`, and let `v` be a direction that vanishes off `supp x ∪ T`, has zero row and
column sums, has zero flux across every cut tight at both `x` and `T`, has all partial double sums
bounded by `64` in absolute value, and is not parallel to `x - T`.  Then the midpoint
`z = (x + T)/2` is the midpoint of `z ± v/512 ∈ P_ASEP^8`, so the segment `[x, T]` is not a face.
-/

namespace ASEP

open Finset

lemma flux_ite (σ : Fin 8 → Fin 8) (S : Finset (Fin 8)) :
    flux (fun i j => if σ i = j then (1 : ℝ) else 0) S = ((S.filter (fun i => σ i ∉ S)).card : ℝ) := by
  unfold flux
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_compl]

theorem not_extreme_of_dir (x v : Fin 8 → Fin 8 → ℝ) (σ : Fin 8 → Fin 8)
    (hx : x ∈ polytope 8)
    (hxe : ∀ i j, x i j = 0 ∨ 1 / 4 ≤ x i j)
    (hxq : ∀ S : Finset (Fin 8), 2 ≤ S.card → S.card ≤ 6 → flux x S = 1 ∨ 5 / 4 ≤ flux x S)
    (hvd : ∀ i, v i i = 0)
    (hvs : ∀ i j, v i j ≠ 0 → x i j ≠ 0 ∨ σ i = j)
    (hvr : ∀ i, ∑ j, v i j = 0) (hvc : ∀ j, ∑ i, v i j = 0)
    (hvcut : ∀ S : Finset (Fin 8), 2 ≤ S.card → S.card ≤ 6 → flux x S = 1 →
      (S.filter (fun i => σ i ∉ S)).card = 1 → flux v S = 0)
    (hvb : ∀ A B : Finset (Fin 8), |∑ i ∈ A, ∑ j ∈ B, v i j| ≤ 64)
    (a1 a2 b1 b2 : Fin 8)
    (hnp : (x a1 a2 - (if σ a1 = a2 then 1 else 0)) * v b1 b2 ≠
      (x b1 b2 - (if σ b1 = b2 then 1 else 0)) * v a1 a2) :
    ¬ IsExtreme ℝ (polytope 8) (segment ℝ x (fun i j => if σ i = j then (1 : ℝ) else 0)) := by
  set T : Fin 8 → Fin 8 → ℝ := fun i j => if σ i = j then (1 : ℝ) else 0 with hTdef
  intro hE
  have hT : T ∈ polytope 8 := hE.1 (right_mem_segment ℝ x T)
  obtain ⟨hxd, hxn, hxc, hxr, hxS⟩ := hx
  obtain ⟨hTd, hTn, hTc, hTr, hTS⟩ := hT
  set δ : ℝ := 1 / 512 with hδ
  set z : Fin 8 → Fin 8 → ℝ := (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • T with hz
  have hT01 : ∀ i j, T i j = 0 ∨ T i j = 1 := by
    intro i j; simp only [hTdef]; split_ifs <;> simp
  have hzij : ∀ i j, z i j = (x i j + T i j) / 2 := by
    intro i j; simp only [hz, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hvabs : ∀ i j, |v i j| ≤ 64 := by
    intro i j; simpa using hvb {i} {j}
  have hfvb : ∀ S : Finset (Fin 8), |flux v S| ≤ 64 := fun S => hvb S Sᶜ
  -- the two points z ± δ v lie in the polytope
  have key : ∀ ε : ℝ, |ε| ≤ δ → z + ε • v ∈ polytope 8 := by
    intro ε hε
    have hεv : ∀ i j, |ε * v i j| ≤ 1 / 8 := by
      intro i j
      rw [abs_mul]
      have := hvabs i j
      have h0 : 0 ≤ |ε| := abs_nonneg ε
      calc |ε| * |v i j| ≤ δ * 64 := mul_le_mul hε this (abs_nonneg _) (by norm_num [hδ])
        _ = 1 / 8 := by norm_num [hδ]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hzij, hxd, hTd, hvd]; ring
    · intro i j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hzij]
      have hxij := hxn i j; have hTij := hTn i j
      by_cases hv : v i j = 0
      · rw [hv]; nlinarith
      · have hb := abs_le.1 (hεv i j)
        rcases hvs i j hv with h | h
        · rcases hxe i j with h' | h'
          · exact absurd h' h
          · nlinarith [hb.1]
        · have : T i j = 1 := by simp [hTdef, h]
          nlinarith [hb.1]
    · intro j
      simp only [hz, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
        hxc, hTc, hvc]; norm_num
    · intro i
      simp only [hz, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
        hxr, hTr, hvr]; norm_num
    · intro S h2 h6
      have h6' : S.card ≤ 6 := by simpa using h6
      have hfl : flux (z + ε • v) S = (flux x S + flux T S) / 2 + ε * flux v S := by
        rw [flux_add, flux_smul, hz, flux_add, flux_smul, flux_smul]; ring
      rw [hfl]
      have hxS1 := hxS S h2 h6
      have hTS1 := hTS S h2 h6
      have hfe : |ε * flux v S| ≤ 1 / 8 := by
        rw [abs_mul]
        calc |ε| * |flux v S| ≤ δ * 64 := mul_le_mul hε (hfvb S) (abs_nonneg _) (by norm_num [hδ])
          _ = 1 / 8 := by norm_num [hδ]
      have hb := abs_le.1 hfe
      have hTcard : flux T S = ((S.filter (fun i => σ i ∉ S)).card : ℝ) := flux_ite σ S
      rcases hxq S h2 h6' with hq | hq
      · by_cases hc : (S.filter (fun i => σ i ∉ S)).card = 1
        · have := hvcut S h2 h6' hq hc
          rw [this, hq, hTcard, hc]; norm_num
        · have hge : (2 : ℝ) ≤ flux T S := by
            rw [hTcard]
            have h1 : (1 : ℝ) ≤ ((S.filter (fun i => σ i ∉ S)).card : ℝ) := by rw [← hTcard]; exact hTS1
            have h1' : 1 ≤ (S.filter (fun i => σ i ∉ S)).card := by exact_mod_cast h1
            have : 2 ≤ (S.filter (fun i => σ i ∉ S)).card := by omega
            exact_mod_cast this
          linarith [hb.1]
      · linarith [hb.1]
  have hp := key δ (by rw [abs_of_pos (by norm_num [hδ])])
  have hq := key (-δ) (by rw [abs_neg, abs_of_pos (by norm_num [hδ])])
  have hzseg : z ∈ segment ℝ x T := ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  have hzo : z ∈ openSegment ℝ (z + (-δ) • v) (z + δ • v) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    funext i j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hpB := hE.2 hq hp hzseg hzo
  clear_value z
  obtain ⟨a, b, ha, hb, hab, hpe⟩ := hpB
  have hcoord : ∀ i j, (-δ) * v i j = (a - 1 / 2) * (x i j - T i j) := by
    intro i j
    have := congrFun (congrFun hpe i) j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hzij] at this
    have hb' : b = 1 - a := by linarith
    rw [hb'] at this; linarith
  apply hnp
  have e1 := hcoord a1 a2
  have e2 := hcoord b1 b2
  have hδ0 : (-δ) ≠ 0 := by norm_num [hδ]
  apply mul_left_cancel₀ hδ0
  show (-δ) * ((x a1 a2 - T a1 a2) * v b1 b2) = (-δ) * ((x b1 b2 - T b1 b2) * v a1 a2)
  calc (-δ) * ((x a1 a2 - T a1 a2) * v b1 b2) = (x a1 a2 - T a1 a2) * ((-δ) * v b1 b2) := by ring
    _ = (x a1 a2 - T a1 a2) * ((a - 1 / 2) * (x b1 b2 - T b1 b2)) := by rw [e2]
    _ = (x b1 b2 - T b1 b2) * ((a - 1 / 2) * (x a1 a2 - T a1 a2)) := by ring
    _ = (x b1 b2 - T b1 b2) * ((-δ) * v a1 a2) := by rw [e1]
    _ = (-δ) * ((x b1 b2 - T b1 b2) * v a1 a2) := by ring

end ASEP
