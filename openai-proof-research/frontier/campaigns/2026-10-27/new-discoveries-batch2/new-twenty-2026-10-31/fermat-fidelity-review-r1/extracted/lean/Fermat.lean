import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
set_option autoImplicit false
open scoped BigOperators
set_option maxRecDepth 2000
namespace Fermat
noncomputable section
abbrev V := Fin 18 → ℝ
def Critical (n d : ℕ) (u x : Fin (n+1) → ℝ) : Prop :=
  x ≠ 0 ∧ (∑ i, x i ^ d) = 0 ∧
    ∀ i j, x i ^ (d-1) * (x j-u j) = x j ^ (d-1) * (x i-u i)
def C : Set V := {x | Critical 17 3 (fun _ => 2) x}
def code (x : V) : Finset (Fin 18) := Finset.univ.filter (fun i => x i = x 0)
lemma a_ne (x : V) (hx : x ∈ C) : x 0 ≠ 0 ∧ x 0 ≠ 2 := by
  obtain ⟨hn, hs, he⟩ := hx
  constructor
  · intro h
    apply hn
    funext i
    have hh := he i 0
    simp only [h] at hh
    norm_num at hh
    simpa using hh
  · intro h
    have hi : ∀ i, x i = 2 := by
      intro i
      have hh := he i 0
      simp only [h] at hh
      norm_num at hh
      linarith
    simp only [hi] at hs
    norm_num at hs
lemma coords (x : V) (hx : x ∈ C) (i : Fin 18) :
    x i = x 0 ∨ x i = 2*x 0/(x 0-2) := by
  have he := hx.2.2 i 0
  norm_num at he
  have hf : (x i - x 0) * ((x 0-2)*x i - 2*x 0) = 0 := by nlinarith [he]
  rcases mul_eq_zero.mp hf with h|h
  · left; linarith
  · right; apply (eq_div_iff (sub_ne_zero.mpr (a_ne x hx).2)).mpr; nlinarith
lemma cube_equation (x : V) (hx : x ∈ C) :
    (code x).card * (x 0-2)^3 + 8*(18-(code x).card : ℝ) = 0 := by
  have ha := a_ne x hx
  have hz : x 0-2 ≠ 0 := sub_ne_zero.mpr ha.2
  have hs := hx.2.1
  have hi : ∀ i, x i ^ 3 * (x 0-2)^3 =
      if i ∈ code x then (x 0)^3*(x 0-2)^3 else 8*(x 0)^3 := by
    intro i
    by_cases h : i ∈ code x
    · simp only [h, ↓reduceIte]
      have : x i = x 0 := (Finset.mem_filter.mp h).2
      rw [this]
    · simp only [h, ↓reduceIte]
      have hn : x i ≠ x 0 := by simpa [code] using h
      have hc := (coords x hx i).resolve_left hn
      rw [hc]
      field_simp
      ring
  have he : (∑ i, x i ^ 3 * (x 0-2)^3) = 0 := by rw [← Finset.sum_mul, hs]; ring
  rw [Finset.sum_congr rfl (fun i _ => hi i)] at he
  rw [Finset.sum_ite] at he
  have hf : Finset.univ.filter (fun i => i ∈ code x) = code x := by ext i; simp
  have hg : Finset.univ.filter (fun i => i ∉ code x) = Finset.univ \ code x := by ext i; simp
  rw [hf, hg] at he
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_sdiff, Finset.card_univ,
    Fintype.card_fin, Finset.inter_univ] at he
  have hc : (code x).card ≤ 18 := by simpa using Finset.card_le_card (Finset.subset_univ (code x))
  rw [Nat.cast_sub hc] at he
  have hh : (x 0)^3 * ((code x).card * (x 0-2)^3 + 8*(18-(code x).card : ℝ)) = 0 := by
    convert he using 1
    push_cast
    ring
  exact (mul_eq_zero.mp hh).resolve_left (pow_ne_zero 3 ha.1)
lemma code_inj : Set.InjOn code C := by
  intro x hx y hy h
  have hp : 0 < (code x).card := Finset.card_pos.mpr ⟨0, by simp [code]⟩
  have hxq := cube_equation x hx
  have hyq := cube_equation y hy
  rw [← h] at hyq
  have hk : (0:ℝ) < (code x).card := by exact_mod_cast hp
  have heq : (x 0-2)^3 = (y 0-2)^3 := by nlinarith
  have ha : x 0 = y 0 := by
    have := (show Odd 3 by decide).pow_injective heq
    linarith
  funext i
  by_cases hi : i ∈ code x
  · have hj : i ∈ code y := h ▸ hi
    simpa [code] using (show x i = y i from ((Finset.mem_filter.mp hi).2).trans (ha.trans (Finset.mem_filter.mp hj).2.symm))
  · have hj : i ∉ code y := by rwa [← h]
    have hxi := (coords x hx i).resolve_left (by simpa [code] using hi)
    have hyi := (coords y hy i).resolve_left (by simpa [code] using hj)
    rw [hxi, hyi, ha]
theorem finite_critical : C.Finite := Set.Finite.of_injOn (Set.mapsTo_univ code C) code_inj (Set.finite_univ)

abbrev Pair := {s : Finset (Fin 18) // s.card = 2}
def point (s : Pair) : V := fun i => if i ∈ s.val then -2 else 1
lemma point_mem (s : Pair) : point s ∈ C := by
  constructor
  · intro h
    have hh := congrFun h 0
    dsimp [point] at hh
    split_ifs at hh <;> norm_num at hh
  constructor
  · have hi : ∀ i, point s i ^ 3 = if i ∈ s.val then (-8:ℝ) else 1 := by
      intro i; simp only [point]; split_ifs <;> norm_num
    change (∑ i, point s i ^ 3) = 0
    rw [Finset.sum_congr rfl (fun i _ => hi i), Finset.sum_ite]
    have hf : Finset.univ.filter (fun i => i ∈ s.val) = s.val := by ext i; simp
    have hg : Finset.univ.filter (fun i => i ∉ s.val) = Finset.univ \ s.val := by ext i; simp
    rw [hf, hg]
    norm_num [Finset.sum_const, Finset.card_sdiff, s.property]
  · intro i j
    dsimp [point]
    split_ifs <;> norm_num
lemma point_inj : Function.Injective point := by
  intro s t h
  apply Subtype.ext
  ext i
  have hh := congrFun h i
  dsimp [point] at hh
  by_cases hs : i ∈ s.val <;> by_cases ht : i ∈ t.val <;> simp_all <;> norm_num at hh
lemma pair_card : Fintype.card Pair = 153 := by
  rw [Fintype.card_finset_len]
  decide
lemma many_critical : 153 ≤ C.ncard := by
  let := finite_critical.fintype
  have h := Fintype.card_le_of_injective (fun s : Pair => (⟨point s, point_mem s⟩ : C))
    (fun a b h => point_inj (congrArg Subtype.val h))
  rw [pair_card] at h
  simpa [Set.ncard, Nat.card_eq_fintype_card] using h
/-- Literal finite-critical-point upper bound in MathDB 328705, with odd degree and
    nonzero smooth points made explicit. It even allows all real observation vectors. -/
def Claim : Prop := ∀ n d : ℕ, 1 ≤ n → 3 ≤ d → Odd d →
  ∀ u : Fin (n+1) → ℝ,
  Set.Finite {x | Critical n d u x} →
  Set.ncard {x | Critical n d u x} ≤ 2*n-1
theorem counterexample : C.Finite ∧ 153 ≤ C.ncard ∧ ¬ C.ncard ≤ 33 := by
  exact ⟨finite_critical, many_critical, by have := many_critical; omega⟩
theorem claim_false : ¬ Claim := by
  intro h
  have hh := h 17 3 (by decide) (by decide) (by decide) (fun _ => 2) finite_critical
  have hm := many_critical
  change C.ncard ≤ 33 at hh
  omega
theorem observation_admissible :
    (∀ _i : Fin 18, (2:ℝ) ≠ 0) ∧ (∑ _i : Fin 18, (2:ℝ)^3) ≠ 0 := by
  norm_num
#print axioms finite_critical
#print axioms point_mem
#print axioms point_inj
#print axioms many_critical
#print axioms observation_admissible
#print axioms counterexample
#print axioms claim_false
end
end Fermat
