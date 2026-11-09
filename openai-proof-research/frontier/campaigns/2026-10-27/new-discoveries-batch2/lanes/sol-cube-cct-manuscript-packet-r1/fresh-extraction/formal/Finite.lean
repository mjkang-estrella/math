import Mathlib.Tactic.NormNum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.Basic
set_option autoImplicit false
set_option warningAsError true
namespace Cube
abbrev V := Fin 32
def bit (v : V) (i : Fin 5) : Bool := v.val.testBit i.val
def zcoord (v : V) (i : Fin 5) : ℤ := if bit v i then -1 else 1
def pairRel (x y u v : V) : Prop := ∀ i, zcoord x i + zcoord y i = zcoord u i + zcoord v i
instance (x y u v : V) : Decidable (pairRel x y u v) := inferInstanceAs (Decidable (∀ i, zcoord x i + zcoord y i = zcoord u i + zcoord v i))
def weight (x y : V) : ℕ := ((Finset.univ : Finset (V × V)).filter fun p => pairRel x y p.1 p.2).card
def Z : Finset V := {2,9,10,13,19,20}
def X : Finset V := Z.erase 9
def Y : Finset V := Z.erase 2
def score (x : V) : ℕ := ∑ y ∈ Z, weight x y
theorem score_preserved (e : V ≃ V) (hw : ∀ x y, weight (e x) (e y) = weight x y)
    (hz : Z.image e = Z) (x : V) : score (e x) = score x := by
  unfold score
  calc
    (∑ y ∈ Z, weight (e x) y) = ∑ y ∈ Z.image e, weight (e x) y := by rw [hz]
    _ = ∑ y ∈ Z, weight (e x) (e y) := Finset.sum_image (fun a _ b _ h => e.injective h)
    _ = ∑ y ∈ Z, weight x y := by simp only [hw]
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
@[simp] theorem w2_2 : weight 2 2 = 1 := by decide +kernel
@[simp] theorem w2_9 : weight 2 9 = 8 := by decide +kernel
@[simp] theorem w2_10 : weight 2 10 = 2 := by decide +kernel
@[simp] theorem w2_13 : weight 2 13 = 16 := by decide +kernel
@[simp] theorem w2_19 : weight 2 19 = 4 := by decide +kernel
@[simp] theorem w2_20 : weight 2 20 = 8 := by decide +kernel
@[simp] theorem w9_2 : weight 9 2 = 8 := by decide +kernel
@[simp] theorem w9_9 : weight 9 9 = 1 := by decide +kernel
@[simp] theorem w9_10 : weight 9 10 = 4 := by decide +kernel
@[simp] theorem w9_13 : weight 9 13 = 2 := by decide +kernel
@[simp] theorem w9_19 : weight 9 19 = 8 := by decide +kernel
@[simp] theorem w9_20 : weight 9 20 = 16 := by decide +kernel
@[simp] theorem w10_2 : weight 10 2 = 2 := by decide +kernel
@[simp] theorem w10_9 : weight 10 9 = 4 := by decide +kernel
@[simp] theorem w10_10 : weight 10 10 = 1 := by decide +kernel
@[simp] theorem w10_13 : weight 10 13 = 8 := by decide +kernel
@[simp] theorem w10_19 : weight 10 19 = 8 := by decide +kernel
@[simp] theorem w10_20 : weight 10 20 = 16 := by decide +kernel
@[simp] theorem w13_2 : weight 13 2 = 16 := by decide +kernel
@[simp] theorem w13_9 : weight 13 9 = 2 := by decide +kernel
@[simp] theorem w13_10 : weight 13 10 = 8 := by decide +kernel
@[simp] theorem w13_13 : weight 13 13 = 1 := by decide +kernel
@[simp] theorem w13_19 : weight 13 19 = 16 := by decide +kernel
@[simp] theorem w13_20 : weight 13 20 = 8 := by decide +kernel
@[simp] theorem w19_2 : weight 19 2 = 4 := by decide +kernel
@[simp] theorem w19_9 : weight 19 9 = 8 := by decide +kernel
@[simp] theorem w19_10 : weight 19 10 = 8 := by decide +kernel
@[simp] theorem w19_13 : weight 19 13 = 16 := by decide +kernel
@[simp] theorem w19_19 : weight 19 19 = 1 := by decide +kernel
@[simp] theorem w19_20 : weight 19 20 = 8 := by decide +kernel
@[simp] theorem w20_2 : weight 20 2 = 8 := by decide +kernel
@[simp] theorem w20_9 : weight 20 9 = 16 := by decide +kernel
@[simp] theorem w20_10 : weight 20 10 = 16 := by decide +kernel
@[simp] theorem w20_13 : weight 20 13 = 8 := by decide +kernel
@[simp] theorem w20_19 : weight 20 19 = 8 := by decide +kernel
@[simp] theorem w20_20 : weight 20 20 = 1 := by decide +kernel
theorem score_unique : ∀ x ∈ Z, score x = score 13 ↔ x = 13 := by
  intro x hx
  simp only [Z, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with h|h|h|h|h|h <;> subst x <;> norm_num [score,Z]
theorem special_weight : weight 9 13 ≠ weight 2 13 := by simp
theorem obstruction (e : V ≃ V) (hw : ∀ x y, weight (e x) (e y) = weight x y)
    (hz : Z.image e = Z) (hxy : X.image e = Y) : False := by
  have h13mem : e 13 ∈ Z := by rw [← hz]; exact Finset.mem_image.mpr ⟨13, by decide, rfl⟩
  have h13 : e 13 = 13 := (score_unique _ h13mem).mp (score_preserved e hw hz 13)
  have h9mem : e 9 ∈ Z := by rw [← hz]; exact Finset.mem_image.mpr ⟨9, by decide, rfl⟩
  have h9not : e 9 ∉ Y := by
    rw [← hxy]
    intro h
    obtain ⟨v,hv,he⟩ := Finset.mem_image.mp h
    have : v = 9 := e.injective he
    subst v
    exact (by decide : (9 : V) ∉ X) hv
  have h9 : e 9 = 2 := by
    by_contra hn
    exact h9not (Finset.mem_erase.mpr ⟨hn,h9mem⟩)
  have he := hw 9 13
  rw [h9,h13] at he
  exact special_weight he.symm
end Cube
