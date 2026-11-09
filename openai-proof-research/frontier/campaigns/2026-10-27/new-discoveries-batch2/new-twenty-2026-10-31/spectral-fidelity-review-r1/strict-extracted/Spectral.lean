import Mathlib
set_option autoImplicit false
namespace SpectralExclusion
noncomputable def value (p : ℕ × ℕ) : ℝ := ((p.1 : ℝ) + Real.sqrt p.2) / 2

def raw (a b c d : ℕ) : ℕ × ℕ := (a+d, (Int.natAbs ((a:ℤ)-d))^2+4*b*c)
def canon (p : ℕ × ℕ) : ℕ × ℕ :=
  if Nat.sqrt p.2 * Nat.sqrt p.2 = p.2 then (p.1 + Nat.sqrt p.2,0) else p

theorem canon_sound (p : ℕ × ℕ) : value (canon p) = value p := by
  unfold canon
  split_ifs with h
  · have hs : Real.sqrt (p.2 : ℝ) = Nat.sqrt p.2 := by
      have hh : (p.2:ℝ) = (Nat.sqrt p.2 : ℝ)^2 := by exact_mod_cast (show p.2 = Nat.sqrt p.2 ^ 2 by nlinarith [h])
      rw [hh, Real.sqrt_sq (by positivity)]
    simp [value, hs]
  · rfl

def incompatible (p q : ℕ × ℕ) : Prop :=
  if p.1 = q.1 then p.2 ≠ q.2 else
    ((p.2:ℤ)-q.2-((q.1:ℤ)-p.1)^2)^2 ≠ 4*((q.1:ℤ)-p.1)^2*q.2
instance (p q : ℕ × ℕ) : Decidable (incompatible p q) := by unfold incompatible; infer_instance

theorem incompatible_sound {p q : ℕ × ℕ} (h : incompatible p q) : value p ≠ value q := by
  intro he
  have hp := Real.sq_sqrt (show (0:ℝ) ≤ p.2 by positivity)
  have hq := Real.sq_sqrt (show (0:ℝ) ≤ q.2 by positivity)
  have he' : (p.1:ℝ) + Real.sqrt p.2 = q.1 + Real.sqrt q.2 := by
    unfold value at he; linarith
  unfold incompatible at h
  split_ifs at h with ht
  · have ht' : (p.1:ℝ) = q.1 := by exact_mod_cast ht
    have hr : Real.sqrt p.2 = Real.sqrt q.2 := by linarith
    have hd : (p.2:ℝ) = q.2 := by rw [hr] at hp; linarith
    exact h (by exact_mod_cast hd)
  · apply h
    have hi : (p.2:ℝ)-q.2-((q.1:ℝ)-p.1)^2 =
        2*((q.1:ℝ)-p.1)*Real.sqrt q.2 := by
      have hr : Real.sqrt p.2 = (q.1:ℝ)-p.1 + Real.sqrt q.2 := by linarith
      rw [hr] at hp
      nlinarith
    have hh : ((p.2:ℝ)-q.2-((q.1:ℝ)-p.1)^2)^2 =
        4*((q.1:ℝ)-p.1)^2*q.2 := by rw [hi]; nlinarith [sq_nonneg ((q.1:ℝ)-p.1)]
    exact_mod_cast hh

def tuples (A : Finset ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) := A ×ˢ A ×ˢ A ×ˢ A
def tupleKey (t : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ := canon (raw t.1 t.2.1 t.2.2.1 t.2.2.2)
noncomputable def omega (A : Finset ℕ) : Finset ℝ := by
  classical
  exact (tuples A).image (fun t => value (raw t.1 t.2.1 t.2.2.1 t.2.2.2))

theorem omega_eq (A : Finset ℕ) : omega A = ((tuples A).image tupleKey).image value := by
  classical
  simp only [omega, Finset.image_image]
  congr 1
  funext t
  exact (canon_sound _).symm

def positiveSet : Finset ℕ := {1,2,4,8,16}
def zeroSet : Finset ℕ := {0,2,3,5,7}
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem positive_keys : ((tuples positiveSet).image tupleKey).card = 115 := by decide +kernel

theorem zero_keys : ((tuples zeroSet).image tupleKey).card = 118 := by decide +kernel

theorem zero_separated : ∀ p ∈ (tuples zeroSet).image tupleKey,
    ∀ q ∈ (tuples zeroSet).image tupleKey, p ≠ q → incompatible p q := by decide +kernel

theorem positive_count_le : (omega positiveSet).card ≤ 115 := by
  rw [omega_eq]
  exact (Finset.card_image_le).trans_eq positive_keys

theorem zero_count : (omega zeroSet).card = 118 := by
  classical
  rw [omega_eq, Finset.card_image_iff.mpr, zero_keys]
  intro p hp q hq he
  by_contra hn
  exact incompatible_sound (zero_separated p hp q hq hn) he

#print axioms positive_count_le
#print axioms zero_count
end SpectralExclusion
