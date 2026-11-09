import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Kirchhoff
open Matrix
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℚ
def Penrose {n : ℕ} (A X : Mat n) : Prop :=
 A * X * A = A ∧ X * A * X = X ∧ (A * X).transpose = A * X ∧ (X * A).transpose = X * A
def GroupInverse {n : ℕ} (A X : Mat n) : Prop :=
 A * X * A = A ∧ X * A * X = X ∧ A * X = X * A
end Kirchhoff
namespace Kirchhoff
open Matrix
theorem penrose_unique {n : ℕ} {A X Y : Mat n} (hX : Penrose A X) (hY : Penrose A Y) : X = Y := by
 obtain ⟨axa, xax, axsym, xasym⟩ := hX
 obtain ⟨aya, yay, aysym, yasym⟩ := hY
 have p : A * X * (A * Y) = A * Y := by rw [← mul_assoc, axa]
 have q : A * Y * (A * X) = A * X := by rw [← mul_assoc, aya]
 have pt := congrArg Matrix.transpose p
 rw [Matrix.transpose_mul, axsym, aysym] at pt
 have axay : A * X = A * Y := q.symm.trans pt
 have r : X * A * (Y * A) = X * A := by rw [mul_assoc X A, ← mul_assoc A Y, aya]
 have s : Y * A * (X * A) = Y * A := by rw [mul_assoc Y A, ← mul_assoc A X, axa]
 have rt := congrArg Matrix.transpose r
 rw [Matrix.transpose_mul, xasym, yasym] at rt
 have xaya : X * A = Y * A := rt.symm.trans s
 calc
  X = X * A * X := xax.symm
  _ = Y * A * X := by rw [xaya]
  _ = Y * (A * Y) := by rw [mul_assoc, axay]
  _ = Y := by simpa only [mul_assoc] using yay

theorem group_unique {n : ℕ} {A X Y : Mat n} (hX : GroupInverse A X) (hY : GroupInverse A Y) : X = Y := by
 obtain ⟨axa, xax, ax⟩ := hX
 obtain ⟨aya, yay, ay⟩ := hY
 have p : A * X * (A * Y) = A * Y := by rw [← mul_assoc, axa]
 have q : A * Y * (A * X) = A * X := by rw [← mul_assoc, aya]
 have axay : A * X = A * Y := by
  calc
   A * X = (A * Y * A) * X := by rw [aya]
   _ = Y * (A * X * A) := by rw [ay]; simp only [mul_assoc]; rw [← ax]
   _ = Y * A := by rw [axa]
   _ = A * Y := ay.symm
 calc
  X = X * A * X := xax.symm
  _ = X * (A * X) := mul_assoc _ _ _
  _ = X * (A * Y) := by rw [axay]
  _ = (A * X) * Y := by rw [← mul_assoc, ← ax]
  _ = (A * Y) * Y := by rw [axay]
  _ = Y * A * Y := by rw [ay]
  _ = Y := by simpa only [mul_assoc] using yay
end Kirchhoff
