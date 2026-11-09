import Encoding
import Mathlib.Combinatorics.SimpleGraph.Maps
namespace Schrijver

theorem stable_iff_add {n : ℕ} [NeZero n] (s : Finset (Fin n)) :
    Stable n s ↔ ∀ i ∈ s, ∀ j ∈ s, j ≠ i + 1 := by
  have hv (i : Fin n) : (i + 1).val = (i.val + 1) % n := by
    simp [Fin.val_add, Nat.add_mod]
  constructor
  · intro hs i hi j hj he
    exact hs i hi j hj (by rw [he, hv])
  · intro hs i hi j hj he
    exact hs i hi j hj (Fin.ext (by rw [hv]; exact he))

def rotateSet {n : ℕ} [NeZero n] (t : Fin n) (s : Finset (Fin n)) : Finset (Fin n) :=
  s.map (Equiv.addRight t).toEmbedding

theorem rotate_stable {n : ℕ} [NeZero n] (t : Fin n) {s : Finset (Fin n)}
    (hs : Stable n s) : Stable n (rotateSet t s) := by
  rw [stable_iff_add] at hs ⊢
  intro i hi j hj he
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hi
  obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hj
  apply hs a ha b hb
  change b + t = (a + t) + 1 at he
  apply add_right_cancel (b := t)
  simpa [add_assoc, add_comm, add_left_comm] using he

def rotateVertex {n k : ℕ} [NeZero n] (t : Fin n) (v : Vertex n k) : Vertex n k :=
  ⟨rotateSet t v.val, by simp [rotateSet, v.property.1], rotate_stable t v.property.2⟩

theorem rotateSet_neg {n : ℕ} [NeZero n] (t : Fin n) (s : Finset (Fin n)) :
    rotateSet (-t) (rotateSet t s) = s := by
  ext i
  simp only [rotateSet, Finset.mem_map, Equiv.toEmbedding_apply, Equiv.coe_addRight]
  constructor
  · rintro ⟨a, ⟨b, hb, rfl⟩, he⟩
    have he' : b = i := by simpa using he
    simpa [he'] using hb
  · intro hi
    exact ⟨i+t, ⟨i, hi, rfl⟩, by simp⟩

noncomputable def rotationEquiv {n k : ℕ} [NeZero n] (t : Fin n) :
    Vertex n k ≃ Vertex n k where
  toFun := rotateVertex t
  invFun := rotateVertex (-t)
  left_inv v := Subtype.ext (rotateSet_neg t v.val)
  right_inv v := Subtype.ext (by
    change rotateSet t (rotateSet (-t) v.val) = v.val
    simpa only [neg_neg] using rotateSet_neg (-t) v.val)

noncomputable def rotationIso {n k : ℕ} [NeZero n] (t : Fin n) : SG n k ≃g SG n k where
  toEquiv := rotationEquiv t
  map_rel_iff' := by
    intro a b
    change (rotateVertex t a ≠ rotateVertex t b ∧
      Disjoint (rotateSet t a.val) (rotateSet t b.val)) ↔ (a ≠ b ∧ Disjoint a.val b.val)
    have hi : rotateVertex t a ≠ rotateVertex t b ↔ a ≠ b :=
      (rotationEquiv (k := k) t).injective.ne_iff
    exact and_congr hi (Finset.disjoint_map _)

-- A mask rotation defined by its literal finite-set action; its bits are aligned below.
noncomputable def rotateMask (n : ℕ) [NeZero n] (t : Fin n) (m : ℕ) : ℕ :=
  encode (rotateSet t (decode n m))

theorem rotateMask_bit {n : ℕ} [NeZero n] (t i : Fin n) (m : ℕ) :
    (rotateMask n t m).testBit (i+t).val = m.testBit i.val := by
  rw [rotateMask, encode_bit]
  have hm : i+t ∈ rotateSet t (decode n m) ↔ i ∈ decode n m := by
    simp [rotateSet]
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  exact hm.trans (by simp [decode])

theorem decode_rotateMask {n : ℕ} [NeZero n] (t : Fin n) (m : ℕ) :
    decode n (rotateMask n t m) = rotateSet t (decode n m) := decode_encode _

end Schrijver
