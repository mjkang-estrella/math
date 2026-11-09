import Graph
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Algebra.Rat
namespace KirchhoffReal
open Matrix
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
def Penrose {n : ℕ} (A X : Mat n) : Prop :=
 A * X * A = A ∧ X * A * X = X ∧ (A * X).transpose = A * X ∧ (X * A).transpose = X * A
def GroupInverse {n : ℕ} (A X : Mat n) : Prop :=
 A * X * A = A ∧ X * A * X = X ∧ A * X = X * A
end KirchhoffReal
namespace KirchhoffReal
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
end KirchhoffReal
namespace KirchhoffReal
open Matrix
noncomputable def liftQ {n} (A : Kirchhoff.Mat n) : Mat n := A.map (algebraMap ℚ ℝ)
theorem lift_mul {n} (A B : Kirchhoff.Mat n) : liftQ (A * B) = liftQ A * liftQ B := by
 exact Matrix.map_mul

theorem lift_penrose {n} {A X : Kirchhoff.Mat n} (h : Kirchhoff.Penrose A X) :
 Penrose (liftQ A) (liftQ X) := by
 obtain ⟨h1,h2,h3,h4⟩ := h
 refine ⟨?_,?_,?_,?_⟩
 · simpa only [lift_mul] using congrArg liftQ h1
 · simpa only [lift_mul] using congrArg liftQ h2
 · simpa only [lift_mul, liftQ, Matrix.transpose_map, Matrix.map_mul] using congrArg liftQ h3
 · simpa only [lift_mul, liftQ, Matrix.transpose_map, Matrix.map_mul] using congrArg liftQ h4

theorem lift_group {n} {A X : Kirchhoff.Mat n} (h : Kirchhoff.GroupInverse A X) :
 GroupInverse (liftQ A) (liftQ X) := by
 obtain ⟨h1,h2,h3⟩ := h
 refine ⟨?_,?_,?_⟩
 · simpa only [lift_mul] using congrArg liftQ h1
 · simpa only [lift_mul] using congrArg liftQ h2
 · simpa only [lift_mul] using congrArg liftQ h3

def pairIndex {n} (X : Mat n) : ℝ := ∑ i, ∑ j, if i < j then X i i + X j j - X i j - X j i else 0
def spectralIndex {n} (X : Mat n) : ℝ := n * Matrix.trace X

theorem lift_pair {n} (X : Kirchhoff.Mat n) : pairIndex (liftQ X) = algebraMap ℚ ℝ (Kirchhoff.pairIndex X) := by
 simp [pairIndex, Kirchhoff.pairIndex, liftQ, map_sum, apply_ite]
theorem lift_spec {n} (X : Kirchhoff.Mat n) : spectralIndex (liftQ X) = algebraMap ℚ ℝ (Kirchhoff.spectralIndex X) := by
 unfold spectralIndex Kirchhoff.spectralIndex Matrix.trace
 rw [map_mul, map_natCast, map_sum]
 rfl

def LiteralConjecture (Inv : {n : ℕ} → Mat n → Mat n → Prop)
 (R : {n : ℕ} → Mat n → ℝ) : Prop :=
 ∀ n, 2 ≤ n → ∀ g : Kirchhoff.Graph n, g.simple.Connected → ∀ a : ℤ, a = 1 ∨ a = -1 →
 ∃ X0 Xa : Mat n, Inv (liftQ (Kirchhoff.laplacian g 0)) X0 ∧
 Inv (liftQ (Kirchhoff.laplacian g a)) Xa ∧
 (if a = 1 then R X0 ≤ R Xa else R Xa ≤ R X0) ∧
 (R Xa = R X0 ↔ Kirchhoff.Regular g)

theorem refuteMP : ¬ LiteralConjecture @Penrose @pairIndex := by
 intro h
 obtain ⟨X0,X1,h0,h1,hle,_⟩ := h 11 (by decide) Kirchhoff.witness Kirchhoff.witness_connected 1 (Or.inl rfl)
 rw [Kirchhoff.lapZero] at h0
 rw [Kirchhoff.lapOne] at h1
 have e0 := penrose_unique h0 (lift_penrose Kirchhoff.validMPZero)
 have e1 := penrose_unique h1 (lift_penrose Kirchhoff.validMPOne)
 simp only [ite_true, e0, e1, lift_pair, Kirchhoff.mp0, Kirchhoff.mp1] at hle
 norm_num at hle

theorem refuteSpec : ¬ LiteralConjecture @GroupInverse @spectralIndex := by
 intro h
 obtain ⟨X0,X1,h0,h1,hle,_⟩ := h 11 (by decide) Kirchhoff.witness Kirchhoff.witness_connected 1 (Or.inl rfl)
 rw [Kirchhoff.lapZero] at h0
 rw [Kirchhoff.lapOne] at h1
 have e0 := group_unique h0 (lift_group Kirchhoff.validGIZero)
 have e1 := group_unique h1 (lift_group Kirchhoff.validGIOne)
 simp only [ite_true, e0, e1, lift_spec, Kirchhoff.gi0, Kirchhoff.gi1] at hle
 norm_num at hle
end KirchhoffReal
