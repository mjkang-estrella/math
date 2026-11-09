import Core
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Nat.Factorization.Basic
namespace Riordan
open Finset Polynomial
noncomputable def h (m : ℕ) : ℕ :=
  if ordCompl[2] (m+1) ∈ ([1,7,9,13] : List ℕ) then 1 else 0

theorem h_binary (m : ℕ) : h m = 0 ∨ h m = 1 := by
  classical
  unfold h
  split_ifs <;> simp

theorem h_io (j : ℕ) : h (2*j+1) = h j := by
  have he : 2*j+1+1 = 2^1*(j+1) := by omega
  simp only [h, he, Nat.ordCompl_self_pow_mul _ _ Nat.prime_two]

theorem oddPart_odd (k : ℕ) : ordCompl[2] (2*k+1) = 2*k+1 := by
  apply (Nat.ordCompl_eq_self_iff_zero_or_not_dvd _ Nat.prime_two).mpr
  right
  omega

theorem h_even (k : ℕ) : h (2*k) =
    if 2*k+1 ∈ ([1,7,9,13] : List ℕ) then 1 else 0 := by
  simp only [h, oddPart_odd]

theorem h_zero : h 0 = 1 := by simpa using h_even 0

theorem h_agrees : ∀ m, m ≤ 13 → h m = gc m := by
  intro m hm
  interval_cases m <;>
    norm_num [gc, show h 0 = 1 from h_zero,
      show h 1 = h 0 from h_io 0,
      show h 3 = h 1 from h_io 1,
      show h 5 = h 2 from h_io 2,
      show h 7 = h 3 from h_io 3,
      show h 9 = h 4 from h_io 4,
      show h 11 = h 5 from h_io 5,
      show h 13 = h 6 from h_io 6,
      show h 2 = 0 from by simpa using h_even 1,
      show h 4 = 0 from by simpa using h_even 2,
      show h 6 = 1 from by simpa using h_even 3,
      show h 8 = 1 from by simpa using h_even 4,
      show h 10 = 0 from by simpa using h_even 5,
      show h 12 = 1 from by simpa using h_even 6]

-- Formal series are their integer coefficient functions. This is the finite
-- convolution defining the coefficient of the kth power, with no convergence.
def seriesPow (a : ℕ → ℤ) : ℕ → ℕ → ℤ :=
  Nat.rec (fun d => if d = 0 then 1 else 0)
    (fun _ prev d => ∑ i ∈ range (d+1), a i * prev (d-i))

theorem seriesPow_succ (a : ℕ → ℤ) (k d : ℕ) :
    seriesPow a (k+1) d = ∑ i ∈ range (d+1), a i * seriesPow a k (d-i) := rfl

theorem seriesPow_local (a b : ℕ → ℤ) (D : ℕ)
    (hab : ∀ d, d ≤ D → a d = b d) :
    ∀ k d, d ≤ D → seriesPow a k d = seriesPow b k d := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
    intro d hd
    rw [seriesPow_succ, seriesPow_succ]
    apply sum_congr rfl
    intro i hi
    rw [hab i (by have := mem_range.mp hi; omega), ih (d-i) (by omega)]

-- The shifted coefficient formula [z^(max-min-1)] a^(min+1) is
-- [z^max] (za)^(min+1), as in the frozen bell_source proof.
def seriesEntry (a : ℕ → ℤ) (i j : ℕ) : ℤ :=
  if i = j then 0 else seriesPow a (min i j+1) (max i j-min i j-1) % 2

theorem seriesEntry_local (a b : ℕ → ℤ) (n : ℕ)
    (hab : ∀ d, d ≤ n-2 → a d = b d) (i j : Fin n) :
    seriesEntry a i j = seriesEntry b i j := by
  by_cases he : i.val = j.val
  · simp [seriesEntry, he]
  · have hd : max i.val j.val - min i.val j.val - 1 ≤ n-2 := by
      have := i.isLt
      have := j.isLt
      omega
    simp only [seriesEntry, he, ite_false, seriesPow_local a b (n-2) hab _ _ hd]

theorem seriesPow_gc (k d : ℕ) :
    seriesPow (fun m => (gc m : ℤ)) k d = (pc k d : ℤ) := by
  induction k generalizing d with
  | zero => simp [seriesPow, pc_zero]
  | succ k ih =>
    simp only [seriesPow_succ, pc_succ, Nat.cast_sum, Nat.cast_mul, ih]

theorem seriesEntry_gc (i j : ℕ) :
    seriesEntry (fun m => (gc m : ℤ)) i j = (entry i j : ℤ) := by
  by_cases he : i = j
  · simp [seriesEntry, entry, he]
  · simp [seriesEntry, entry, he, seriesPow_gc, Int.natCast_emod]

noncomputable def hZ (m : ℕ) : ℤ := h m

theorem h_witness (i j : Fin 15) : seriesEntry hZ i j = (entry i j : ℤ) := by
  rw [seriesEntry_local hZ (fun m => (gc m : ℤ)) 15
    (by intro d hd; simp only [hZ, h_agrees d hd]) i j, seriesEntry_gc]
end Riordan
