import Certificates
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Algebra.Ring.Int.Parity
namespace Kirchhoff
open Matrix
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
structure Graph (n : ℕ) where
 adj : Fin n → Fin n → Bool
 symm : ∀ i j, adj i j = adj j i
 loopless : ∀ i, adj i i = false

def Graph.simple {n} (g : Graph n) : SimpleGraph (Fin n) where
 Adj i j := g.adj i j = true
 symm := ⟨fun i j h => by rwa [g.symm] at h⟩
 loopless := ⟨fun i h => by simp [g.loopless] at h⟩

instance {n} (g : Graph n) : DecidableRel g.simple.Adj :=
 fun i j => inferInstanceAs (Decidable (g.adj i j = true))

def degree {n} (g : Graph n) (i : Fin n) : ℕ := ∑ j, if g.adj i j then 1 else 0

def Kpow {n} (g : Graph n) (a : ℤ) : Mat n := Matrix.diagonal (fun i => (degree g i : ℚ) ^ a)
def weight {n} (g : Graph n) (a : ℤ) (i j : Fin n) : ℚ :=
 if g.adj i j then (degree g i : ℚ) ^ a * (degree g j : ℚ) ^ (-a) else 0
def laplacian {n} (g : Graph n) (a : ℤ) : Mat n :=
 fun i j => (if i = j then ∑ k, weight g a i k else 0) - weight g a i j

def witness : Graph 11 where
 adj i j := decide ((i.val < 6 ∧ j.val < 6 ∧ i ≠ j) ∨
   (i = 0 ∧ j = 6) ∨ (j = 0 ∧ i = 6) ∨
   (6 ≤ i.val ∧ i.val + 1 = j.val) ∨ (6 ≤ j.val ∧ j.val + 1 = i.val))
 symm := by decide +kernel
 loopless := by decide +kernel

theorem witness_connected : witness.simple.Connected := by
 rw [SimpleGraph.connected_iff_exists_forall_reachable]
 refine ⟨0, ?_⟩
 have r6 : witness.simple.Reachable 0 6 := SimpleGraph.Adj.reachable (by decide +kernel)
 have r7 : witness.simple.Reachable 0 7 := r6.trans (SimpleGraph.Adj.reachable (by decide +kernel))
 have r8 : witness.simple.Reachable 0 8 := r7.trans (SimpleGraph.Adj.reachable (by decide +kernel))
 have r9 : witness.simple.Reachable 0 9 := r8.trans (SimpleGraph.Adj.reachable (by decide +kernel))
 have r10 : witness.simple.Reachable 0 10 := r9.trans (SimpleGraph.Adj.reachable (by decide +kernel))
 intro i
 fin_cases i
 · exact SimpleGraph.Reachable.refl _
 · exact SimpleGraph.Adj.reachable (by decide +kernel)
 · exact SimpleGraph.Adj.reachable (by decide +kernel)
 · exact SimpleGraph.Adj.reachable (by decide +kernel)
 · exact SimpleGraph.Adj.reachable (by decide +kernel)
 · exact SimpleGraph.Adj.reachable (by decide +kernel)
 · exact r6
 · exact r7
 · exact r8
 · exact r9
 · exact r10

theorem lapZero : laplacian witness 0 = LZero := by decide +kernel
theorem lapOne : laplacian witness 1 = LOne := by decide +kernel
noncomputable def mp {n} (A : Mat n) : Mat n := by
 classical
 exact if h : ∃ X, Penrose A X then Classical.choose h else 0
noncomputable def gi {n} (A : Mat n) : Mat n := by
 classical
 exact if h : ∃ X, GroupInverse A X then Classical.choose h else 0

theorem mp_eq {n} {A X : Mat n} (h : Penrose A X) : mp A = X := by
 unfold mp
 rw [dite_eq_left ⟨X,h⟩]
 exact penrose_unique (Classical.choose_spec (show ∃ X, Penrose A X from ⟨X,h⟩)) h

theorem gi_eq {n} {A X : Mat n} (h : GroupInverse A X) : gi A = X := by
 unfold gi
 rw [dite_eq_left ⟨X,h⟩]
 exact group_unique (Classical.choose_spec (show ∃ X, GroupInverse A X from ⟨X,h⟩)) h
noncomputable def resistance {n} (g : Graph n) (a : ℤ) (i j : Fin n) : ℚ :=
 let X := mp (laplacian g a)
 X i i + X j j - X i j - X j i
noncomputable def indexMP {n} (g : Graph n) (a : ℤ) : ℚ := pairIndex (mp (laplacian g a))
noncomputable def indexSpec {n} (g : Graph n) (a : ℤ) : ℚ := spectralIndex (gi (laplacian g a))
def Regular {n} (g : Graph n) : Prop := ∃ d, ∀ i, degree g i = d

def Conjecture (R : {n : ℕ} → Graph n → ℤ → ℚ) : Prop :=
 ∀ n, 2 ≤ n → ∀ g : Graph n, g.simple.Connected → ∀ a : ℤ, a = 1 ∨ a = -1 →
 (if a = 1 then R g 0 ≤ R g a else R g a ≤ R g 0) ∧
 (R g a = R g 0 ↔ Regular g)

theorem mp_value_zero : indexMP witness 0 = 370/3 := by
 rw [indexMP, lapZero, mp_eq validMPZero, mp0]
theorem mp_value_one : indexMP witness 1 = 515538204/7137235 := by
 rw [indexMP, lapOne, mp_eq validMPOne, mp1]
theorem spec_value_zero : indexSpec witness 0 = 370/3 := by
 rw [indexSpec, lapZero, gi_eq validGIZero, gi0]
theorem spec_value_one : indexSpec witness 1 = 1696684/14035 := by
 rw [indexSpec, lapOne, gi_eq validGIOne, gi1]
theorem refuteMP : ¬ Conjecture @indexMP := by
 intro h
 have bad := (h 11 (by decide +kernel) witness witness_connected 1 (Or.inl rfl)).1
 simp only [ite_true] at bad
 rw [mp_value_zero, mp_value_one] at bad
 norm_num at bad
theorem refuteSpec : ¬ Conjecture @indexSpec := by
 intro h
 have bad := (h 11 (by decide +kernel) witness witness_connected 1 (Or.inl rfl)).1
 simp only [ite_true] at bad
 rw [spec_value_zero, spec_value_one] at bad
 norm_num at bad
end Kirchhoff
namespace Kirchhoff
open Matrix
theorem resistance_sum {n} (g : Graph n) (a : ℤ) :
 indexMP g a = ∑ i, ∑ j, if i < j then resistance g a i j else 0 := rfl

def adjacency {n} (g : Graph n) : Mat n := fun i j => if g.adj i j then 1 else 0

theorem laplacian_source_formula {n} (g : Graph n) (a : ℤ) :
 laplacian g a = Matrix.diagonal (fun i => ∑ k, weight g a i k) -
 Kpow g a * adjacency g * Kpow g (-a) := by
 ext i j
 simp only [laplacian, Kpow, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.sub_apply,
  Matrix.diagonal_apply, adjacency, weight]
 split <;> simp_all

theorem witness_degrees : (fun i => degree witness i) = ![6,5,5,5,5,5,2,2,2,2,1] := by decide +kernel

theorem primary_strict : indexMP witness 1 < indexMP witness 0 := by
 rw [mp_value_one, mp_value_zero]
 norm_num

theorem secondary_strict : indexSpec witness 1 < indexSpec witness 0 := by
 rw [spec_value_one, spec_value_zero]
 norm_num
end Kirchhoff
namespace Kirchhoff
/-- The source claim with inverse existence stated explicitly, avoiding any default
value for matrices without an inverse of the required kind. -/
def LiteralConjecture (Inv : {n : ℕ} → Mat n → Mat n → Prop)
 (R : {n : ℕ} → Mat n → ℚ) : Prop :=
 ∀ n, 2 ≤ n → ∀ g : Graph n, g.simple.Connected → ∀ a : ℤ, a = 1 ∨ a = -1 →
 ∃ X0 Xa : Mat n, Inv (laplacian g 0) X0 ∧ Inv (laplacian g a) Xa ∧
 (if a = 1 then R X0 ≤ R Xa else R Xa ≤ R X0) ∧
 (R Xa = R X0 ↔ Regular g)

theorem refuteLiteralMP : ¬ LiteralConjecture @Penrose @pairIndex := by
 intro h
 obtain ⟨X0, X1, h0, h1, hle, _⟩ := h 11 (by decide) witness witness_connected 1 (Or.inl rfl)
 rw [lapZero] at h0
 rw [lapOne] at h1
 have e0 := penrose_unique h0 validMPZero
 have e1 := penrose_unique h1 validMPOne
 simp only [ite_true, e0, e1, mp0, mp1] at hle
 norm_num at hle

theorem refuteLiteralSpec : ¬ LiteralConjecture @GroupInverse @spectralIndex := by
 intro h
 obtain ⟨X0, X1, h0, h1, hle, _⟩ := h 11 (by decide) witness witness_connected 1 (Or.inl rfl)
 rw [lapZero] at h0
 rw [lapOne] at h1
 have e0 := group_unique h0 validGIZero
 have e1 := group_unique h1 validGIOne
 simp only [ite_true, e0, e1, gi0, gi1] at hle
 norm_num at hle
end Kirchhoff
