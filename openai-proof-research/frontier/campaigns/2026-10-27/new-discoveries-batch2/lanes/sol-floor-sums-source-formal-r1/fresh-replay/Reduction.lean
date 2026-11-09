import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
set_option warningAsError true
namespace FloorSums
open Finset

def clip (H : ℕ) (u : ℤ) : ℤ := max 0 (min (H : ℤ) u)

theorem threshold_count (H : ℕ) (s r : ℤ) :
    (∑ j ∈ range H, if r ≤ (j : ℤ) + s then (1 : ℤ) else 0) =
      clip H (s + H - r) := by
  induction H with
  | zero => simp [clip]
  | succ H ih =>
    rw [sum_range_succ, ih]
    simp only [clip, Nat.cast_add, Nat.cast_one, min_def, max_def]
    split_ifs <;> omega

theorem quotient_thresholds (m n : ℕ) (_hm : 0 < m) (hn : n < 5*m) :
    ((n / m : ℕ) : ℤ) =
      (if m ≤ n then (1 : ℤ) else 0) +
      (if 2*m ≤ n then (1 : ℤ) else 0) +
      (if 3*m ≤ n then (1 : ℤ) else 0) +
      (if 4*m ≤ n then (1 : ℤ) else 0) := by
  by_cases h1 : n < m
  · rw [Nat.div_eq_of_lt h1]
    simp [show ¬m ≤ n by omega, show ¬2*m ≤ n by omega,
      show ¬3*m ≤ n by omega, show ¬4*m ≤ n by omega]
  by_cases h2 : n < 2*m
  · have hq : n / m = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    simp [hq, show m ≤ n by omega, show ¬2*m ≤ n by omega,
      show ¬3*m ≤ n by omega, show ¬4*m ≤ n by omega]
  by_cases h3 : n < 3*m
  · have hq : n / m = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
    simp [hq, show m ≤ n by omega, show 2*m ≤ n by omega,
      show ¬3*m ≤ n by omega, show ¬4*m ≤ n by omega]
  by_cases h4 : n < 4*m
  · have hq : n / m = 3 := Nat.div_eq_of_lt_le (by omega) (by omega)
    simp [hq, show m ≤ n by omega, show 2*m ≤ n by omega,
      show 3*m ≤ n by omega, show ¬4*m ≤ n by omega]
  · have hq : n / m = 4 := Nat.div_eq_of_lt_le (by omega) (by omega)
    simp [hq, show m ≤ n by omega, show 2*m ≤ n by omega,
      show 3*m ≤ n by omega, show 4*m ≤ n by omega]

theorem prefix_clips (m H s : ℕ) (hm : 0 < m) (hH : H ≤ m) (hs : s ≤ 4*(m-1)) :
    (∑ j ∈ range H, (((j+s)/m : ℕ) : ℤ)) =
      clip H ((s : ℤ)+H-m) + clip H ((s : ℤ)+H-2*m) +
      clip H ((s : ℤ)+H-3*m) + clip H ((s : ℤ)+H-4*m) := by
  have he (j : ℕ) (hj : j ∈ range H) :=
    quotient_thresholds m (j+s) hm (by have := mem_range.mp hj; omega)
  rw [sum_congr rfl he]
  simp only [sum_add_distrib]
  have hc (q : ℕ) :
      (∑ j ∈ range H, if q*m ≤ j+s then (1 : ℤ) else 0) =
        clip H ((s : ℤ)+H-(q*m : ℕ)) := by
    convert threshold_count H (s : ℤ) (q*m : ℕ) using 1
    apply sum_congr rfl
    intro j _
    congr 1
    norm_cast
  have hc1 := hc 1
  simp only [one_mul] at hc1
  rw [hc1, hc 2, hc 3, hc 4]
  norm_num

def literalSum (m K : ℕ) (a : Fin 4 → ℕ) : ℤ :=
  ∑ j ∈ range (K+1), ∑ T ∈ (univ : Finset (Fin 4)).powerset,
    (-1 : ℤ)^(4-T.card) * (((j + ∑ i ∈ T, a i)/m : ℕ) : ℤ)

def clampedSum (m H : ℕ) (a : Fin 4 → ℕ) : ℤ :=
  ∑ T ∈ (univ : Finset (Fin 4)).powerset, (-1 : ℤ)^(4-T.card) *
    (clip H ((∑ i ∈ T, a i : ℕ)+ (H : ℤ)-m) +
     clip H ((∑ i ∈ T, a i : ℕ)+ (H : ℤ)-2*m) +
     clip H ((∑ i ∈ T, a i : ℕ)+ (H : ℤ)-3*m) +
     clip H ((∑ i ∈ T, a i : ℕ)+ (H : ℤ)-4*m))

def LiteralEndpoint : Prop := ∀ (m : ℕ), 0 < m → ∀ (a : Fin 4 → ℕ),
  (∀ i, a i < m) → ∀ K : ℕ, K < m → -3 * (m/3 : ℕ) ≤ literalSum m K a

theorem sixteen_subsets : (univ : Finset (Fin 4)).powerset.card = 16 := by decide

theorem prefix_parameters (m K : ℕ) : K < m ↔ 1 ≤ K+1 ∧ K+1 ≤ m := by omega

theorem residue_parameters (m t : ℕ) : t = m/3 ↔ 3*t ≤ m ∧ m ≤ 3*t+2 := by omega

theorem actual_floor (n m : ℕ) : ⌊((n : ℚ) / (m : ℚ))⌋ = ((n/m : ℕ) : ℤ) := by
  exact Rat.floor_natCast_div_natCast n m

theorem subset_sum_bound (m : ℕ) (a : Fin 4 → ℕ) (ha : ∀ i, a i < m)
    (T : Finset (Fin 4)) : (∑ i ∈ T, a i) ≤ 4*(m-1) := by
  calc
    (∑ i ∈ T, a i) ≤ ∑ i ∈ T, (m-1) := sum_le_sum (fun i _ => by have := ha i; omega)
    _ = T.card * (m-1) := by simp
    _ ≤ 4*(m-1) := Nat.mul_le_mul_right _ (by
      have h := card_le_card (subset_univ T)
      simpa using h)

theorem literal_eq_clamped (m K : ℕ) (a : Fin 4 → ℕ) (hm : 0 < m)
    (ha : ∀ i, a i < m) (hK : K < m) :
    literalSum m K a = clampedSum m (K+1) a := by
  unfold literalSum clampedSum
  rw [sum_comm]
  apply sum_congr rfl
  intro T _
  rw [← mul_sum, prefix_clips m (K+1) (∑ i ∈ T, a i) hm (by omega)
    (subset_sum_bound m a ha T)]

theorem source_floor_sum (m K : ℕ) (a : Fin 4 → ℕ) :
    (∑ j ∈ range (K+1), ∑ T ∈ (univ : Finset (Fin 4)).powerset,
      (-1 : ℤ)^(4-T.card) * ⌊(((j + ∑ i ∈ T, a i : ℕ) : ℚ)/(m : ℚ))⌋) =
      literalSum m K a := by
  simp only [actual_floor, literalSum]

end FloorSums
