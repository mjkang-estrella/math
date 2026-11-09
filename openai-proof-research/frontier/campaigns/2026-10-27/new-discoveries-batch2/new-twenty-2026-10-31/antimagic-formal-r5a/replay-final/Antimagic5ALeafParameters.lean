import Antimagic5AInternal
namespace Antimagic.Round5A
open Round4A Finset

def tupleParameter (Z q p : ℕ) : ℕ := if Z < p then p - Z else q + 1 + p - Z

theorem tupleParameter_shell (Z k r : ℕ) (hk : k < Z) (hr : r < 2 * k) :
    tupleParameter Z (2 * k) (shellEntry Z r) =
      if r % 2 = 0 then 2 * k - r / 2 else 1 + r / 2 := by
  unfold tupleParameter shellEntry
  split_ifs <;> omega

theorem tupleParameter_range (Z k r : ℕ) (hk : k < Z) (hr : r < 2 * k) :
    1 ≤ tupleParameter Z (2 * k) (shellEntry Z r) ∧
    tupleParameter Z (2 * k) (shellEntry Z r) ≤ 2 * k := by
  rw [tupleParameter_shell Z k r hk hr]
  split_ifs <;> omega

theorem tupleParameter_injective (Z k : ℕ) (hk : k < Z) :
    Function.Injective (fun r : Fin (2 * k) => tupleParameter Z (2 * k) (shellEntry Z r.val)) := by
  intro r u eq
  dsimp only at eq
  rw [tupleParameter_shell Z k r.val hk r.isLt, tupleParameter_shell Z k u.val hk u.isLt] at eq
  have hr := r.isLt
  have hu := u.isLt
  apply Fin.ext
  split_ifs at eq <;> omega

/-- The displacement exactly cancels the parent shell displacement. -/
theorem tupleParameter_cancel (Z k r : ℕ) (hk : k < Z) (hr : r < 2 * k) :
    shellEntry Z r + tupleParameter Z (2 * k) (shellEntry Z r) =
      Z + sigma k (tupleParameter Z (2 * k) (shellEntry Z r)) := by
  rw [tupleParameter_shell Z k r hk hr]
  unfold shellEntry sigma
  split_ifs <;> omega

theorem even_power (t h : ℕ) (he : Even t) (hh : 1 ≤ h) : t ^ h = 2 * (t ^ h / 2) := by
  have hd := (even_iff_two_dvd.mp he).trans (dvd_pow_self t (by omega : h ≠ 0))
  omega

theorem last_shell_bound (t n : ℕ) (he : Even t) (hn : 3 ≤ n) :
    t ^ (n - 1) / 2 < center t n := by
  have hs := internalEdges_split t n (by omega)
  have hz := shell_size t n he hn
  have hZ : 1 ≤ center t n := by simp [center]
  have ht := offset_top t n (n-1) (by omega)
  have hp := even_power t (n-1) he (by omega)
  have hle : t ^ (n-1) ≤ offset t n 1 := by
    have hstep := offset_step t n (n-2) (by omega)
    have hm := offset_mono t n (show 1 ≤ n-2 by omega)
    rw [show n-2+1=n-1 by omega, offset_top t n (n-1) (by omega)] at hstep
    omega
  omega

theorem last_internal_shell (t n i : ℕ) (ht : 4 ≤ t) (hn : 3 ≤ n) :
    internalLabel t n (n-1) i = shellEntry (center t n) i := by
  rw [internalLabel_shell t n (n-1) i (by omega), unpatched t (n-1) i ht,
    offset_top t n (n-1) (by omega), Nat.zero_add]

/-- Parent-derived tuple coordinates are a permutation on the actual last row. -/
def parentParameter (t n i : ℕ) : ℕ :=
  tupleParameter (center t n) (t ^ (n-1)) (internalLabel t n (n-1) i)

theorem parentParameter_range (t n i : ℕ) (ht : 4 ≤ t) (he : Even t) (hn : 3 ≤ n)
    (hi : i < t ^ (n-1)) : 1 ≤ parentParameter t n i ∧ parentParameter t n i ≤ t ^ (n-1) := by
  have hp := even_power t (n-1) he (by omega)
  unfold parentParameter
  rw [last_internal_shell t n i ht hn]
  nth_rw 1 [hp]
  simpa only [← hp] using tupleParameter_range (center t n) (t ^ (n-1)/2) i
    (last_shell_bound t n he hn) (by omega)

theorem parentParameter_injective (t n : ℕ) (ht : 4 ≤ t) (he : Even t) (hn : 3 ≤ n) :
    Function.Injective (fun i : Fin (t ^ (n-1)) => parentParameter t n i.val) := by
  intro i j eq
  have hp := even_power t (n-1) he (by omega)
  unfold parentParameter at eq
  dsimp only at eq
  rw [last_internal_shell t n i.val ht hn, last_internal_shell t n j.val ht hn] at eq
  conv at eq => lhs; arg 2; rw [hp]
  conv at eq => rhs; arg 2; rw [hp]
  have hij := tupleParameter_injective (center t n) (t ^ (n-1)/2)
    (last_shell_bound t n he hn) (a₁ := ⟨i.val,by have := i.isLt; omega⟩)
    (a₂ := ⟨j.val,by have := j.isLt; omega⟩) eq
  exact Fin.ext (congrArg (fun a : Fin (2*((t^(n-1))/2)) => a.val) hij)

def parentMap (t n : ℕ) (ht : 4 ≤ t) (he : Even t) (hn : 3 ≤ n)
    (i : Fin (t ^ (n-1))) : Fin (t ^ (n-1)) :=
  ⟨parentParameter t n i.val - 1, by have := parentParameter_range t n i.val ht he hn i.isLt; omega⟩

theorem parentMap_bijective (t n : ℕ) (ht : 4 ≤ t) (he : Even t) (hn : 3 ≤ n) :
    Function.Bijective (parentMap t n ht he hn) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_,rfl⟩
  intro i j eq
  apply parentParameter_injective t n ht he hn
  change parentParameter t n i.val = parentParameter t n j.val
  have hi := parentParameter_range t n i.val ht he hn i.isLt
  have hj := parentParameter_range t n j.val ht he hn j.isLt
  have h := congrArg Fin.val eq
  change parentParameter t n i.val - 1 = parentParameter t n j.val - 1 at h
  omega

#print axioms parentMap_bijective
#print axioms tupleParameter_cancel
end Antimagic.Round5A
