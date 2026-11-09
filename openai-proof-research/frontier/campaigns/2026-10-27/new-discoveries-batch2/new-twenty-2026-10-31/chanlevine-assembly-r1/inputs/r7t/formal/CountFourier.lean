import CountArithmetic
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
open scoped BigOperators
namespace ChanLevine
variable {n : ℕ} [NeZero n] {F : Type*} [Field F] [CharZero F]

def finiteFourier (χ : AddChar (ZMod n) F) (f : ZMod n → F) (k : ZMod n) : F :=
  ∑ j, χ (-(j*k)) * f j

omit [CharZero F] in
theorem fourier_inversion (χ : AddChar (ZMod n) F) (hp : χ.IsPrimitive)
    (f : ZMod n → F) (i : ZMod n) :
    (∑ k, χ (i*k) * finiteFourier χ f k) = (n : F) * f i := by
  have orth (t : ZMod n) : (∑ k, χ (t*k)) = if t = 0 then (n : F) else 0 := by
    by_cases ht : t = 0
    · simp [ht, AddChar.map_zero_eq_one]
    · simp only [ht, ite_false]
      exact AddChar.sum_eq_zero_of_ne_one (hp ht)
  simp only [finiteFourier, Finset.mul_sum]
  rw [Finset.sum_comm]
  have he (j k : ZMod n) : χ (i*k) * (χ (-(j*k)) * f j) =
      χ ((i-j)*k) * f j := by
    rw [← mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  simp_rw [he, ← Finset.sum_mul, orth]
  simp [sub_eq_zero]

theorem finiteFourier_injective (χ : AddChar (ZMod n) F) (hp : χ.IsPrimitive) :
    Function.Injective (finiteFourier χ) := by
  intro f g h
  funext i
  have he := fourier_inversion χ hp f i
  rw [h, fourier_inversion χ hp g i] at he
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne n)) he.symm

omit [CharZero F] in
theorem fourier_unit (χ : AddChar (ZMod n) F) (f : ZMod n → F)
    (u : (ZMod n)ˣ) (k : ZMod n) :
    finiteFourier χ (fun j => f ((u : ZMod n)*j)) k =
    finiteFourier χ f ((↑u⁻¹ : ZMod n)*k) := by
  apply Fintype.sum_equiv u.mulLeft
  intro j
  simp only [Units.mulLeft_apply]
  congr 2
  simp [mul_assoc, mul_left_comm]

omit [NeZero n] in
theorem addOrderOf_unit_mul (u : (ZMod n)ˣ) (k : ZMod n) :
    addOrderOf ((u : ZMod n)*k) = addOrderOf k := by
  let f : ZMod n →+ ZMod n :=
    { toFun := fun x => (u : ZMod n)*x
      map_zero' := mul_zero _
      map_add' := mul_add _ }
  exact addOrderOf_injective f u.mulLeft.injective k

noncomputable def countingChar (n : ℕ) [NeZero n] :
    AddChar.PrimitiveAddChar (ZMod n) ℚ :=
  AddChar.primitiveZModChar ⟨n, NeZero.pos n⟩ ℚ (Nat.cast_ne_zero.mpr (NeZero.ne n))
abbrev CountingField (n : ℕ) [NeZero n] := CyclotomicField (countingChar n).n ℚ
noncomputable def countVector (n m : ℕ) [NeZero n] : ZMod n → CountingField n :=
  fun i => testCount n m i

/-- OPEN analytic sublemma. The frequency's additive order determines the
Fourier coefficient. This is the root-of-unity/transfer-matrix evaluation. -/
def SpectralOrder : Prop :=
  ∀ (n m : ℕ) [NeZero n], 3 ≤ n → 1 ≤ m → ∀ k l : ZMod n,
    addOrderOf k = addOrderOf l →
    finiteFourier (countingChar n).char (countVector n m) k =
    finiteFourier (countingChar n).char (countVector n m) l

theorem unitCount_of_spectralOrder (hs : SpectralOrder) : UnitCount := by
  intro n m _ hn hm u i
  have he : (fun j => countVector n m ((u : ZMod n)*j)) = countVector n m := by
    apply finiteFourier_injective (countingChar n).char (countingChar n).prim
    funext k
    rw [fourier_unit]
    exact hs n m hn hm _ _ (addOrderOf_unit_mul u⁻¹ k)
  have hi := congrFun he i
  change (testCount n m ((u : ZMod n)*i) : CountingField n) =
    (testCount n m i : CountingField n) at hi
  exact_mod_cast hi
end ChanLevine
