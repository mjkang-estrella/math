import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic
set_option maxRecDepth 3000
set_option synthInstance.maxSize 1000
set_option maxHeartbeats 3000000
namespace Rainbow
open SimpleGraph
def adj (x y : Fin 8) : Prop :=
  (![202,225,232,149,232,22,23,31] : Fin 8 → Nat) x |> fun z => z.testBit y.val = true
instance (x y : Fin 8) : Decidable (adj x y) := inferInstanceAs (Decidable (_ = true))
def G : SimpleGraph (Fin 8) where
  Adj := adj
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩
instance : DecidableRel G.Adj := fun _ _ => inferInstanceAs (Decidable (adj _ _))

-- Deleting the pair xy, and deleting S by isolating its vertices.
def cutGraph {V : Type*} (H : SimpleGraph V) (S : V → Prop) (x y : V) : SimpleGraph V where
  Adj u v := H.Adj u v ∧ ¬ S u ∧ ¬ S v ∧ ¬ (u = x ∧ v = y) ∧ ¬ (u = y ∧ v = x)
  symm := ⟨by intro u v h; exact ⟨h.1.symm,h.2.2.1,h.2.1, fun z => h.2.2.2.2 z.symm, fun z => h.2.2.2.1 z.symm⟩⟩
  loopless := ⟨by intro u h; exact H.irrefl h.1⟩

def RainbowOn {V C : Type*} (c : V → C) (S : V → Prop) : Prop :=
  ∀ u v, S u → S v → c u = c v → u = v

def Valid {V : Type*} (H : SimpleGraph V) {k : Nat} (c : V → Fin k) : Prop :=
  ∀ x y, x ≠ y → ∃ S : V → Prop, ¬ S x ∧ ¬ S y ∧
    RainbowOn c S ∧
    (H.Adj x y → (∀ v, S v → c v ≠ c x) ∨ (∀ v, S v → c v ≠ c y)) ∧
    ¬ (cutGraph H S x y).Reachable x y

noncomputable def rvd {V : Type*} (H : SimpleGraph V) : Nat :=
  sInf {k : Nat | ∃ c : V → Fin k, Valid H c}

def CutCert {V C : Type*} (H : SimpleGraph V) (c : V → C)
    (x y : V) (S A : V → Prop) : Prop :=
  ¬ S x ∧ ¬ S y ∧ RainbowOn c S ∧
  (H.Adj x y → (∀ v, S v → c v ≠ c x) ∨ (∀ v, S v → c v ≠ c y)) ∧
  A x ∧ ¬ A y ∧
  (∀ u v, A u → ¬ S u → ¬ S v → H.Adj u v →
    ¬ (u = x ∧ v = y) → ¬ (u = y ∧ v = x) → A v)

theorem cert_sound {V : Type*} {H : SimpleGraph V} {k : Nat} {c : V → Fin k}
    {x y : V} {S A : V → Prop} (h : CutCert H c x y S A) :
    ¬ (cutGraph H S x y).Reachable x y := by
  intro ⟨p⟩
  have keep : ∀ {u v}, (cutGraph H S x y).Walk u v → A u → A v := by
    intro u v w
    induction w with
    | nil => exact id
    | @cons u v z huv w ih =>
      intro hu
      exact ih (h.2.2.2.2.2.2 u v hu huv.2.1 huv.2.2.1 huv.1 huv.2.2.2.1 huv.2.2.2.2)
  exact h.2.2.2.2.2.1 (keep p h.2.2.2.2.1)

theorem valid_of_certs {V : Type*} {H : SimpleGraph V} {k : Nat} {c : V → Fin k}
    (S A : V → V → V → Prop)
    (h : ∀ x y, x ≠ y → CutCert H c x y (S x y) (A x y)) : Valid H c := by
  intro x y hxy
  obtain h := h x y hxy
  exact ⟨S x y, h.1,h.2.1,h.2.2.1,h.2.2.2.1,cert_sound h⟩
def color0 (v : Fin 8) : Fin 4 := ![0, 1, 2, 2, 3, 0, 3, 1] v
def cut0 (x y : Fin 8) (v : Fin 8) : Prop := (![0, 200, 232, 148, 232, 22, 22, 74, 200, 0, 232, 149, 232, 20, 21, 21, 232, 232, 0, 145, 232, 18, 19, 104, 148, 149, 145, 0, 133, 22, 23, 21, 232, 232, 232, 133, 0, 6, 7, 104, 22, 20, 18, 22, 6, 0, 22, 22, 22, 21, 19, 23, 7, 22, 0, 23, 74, 21, 104, 21, 104, 22, 23, 0] : Fin 64 → Nat) ⟨x.val * 8 + y.val, by omega⟩ |> fun z => z.testBit v.val = true
def side0 (x y : Fin 8) (v : Fin 8) : Prop := (![0, 1, 3, 99, 3, 201, 137, 1, 54, 0, 3, 98, 3, 203, 170, 98, 4, 4, 0, 102, 4, 205, 172, 4, 8, 8, 8, 0, 8, 201, 136, 8, 16, 16, 16, 114, 0, 217, 184, 16, 32, 32, 32, 32, 32, 0, 32, 32, 64, 64, 64, 64, 64, 201, 0, 64, 180, 136, 147, 226, 135, 201, 136, 0] : Fin 64 → Nat) ⟨x.val * 8 + y.val, by omega⟩ |> fun z => z.testBit v.val = true
instance (x y : Fin 8) (v : Fin 8) : Decidable (cut0 x y v) := inferInstanceAs (Decidable (_ = true))
instance (x y : Fin 8) (v : Fin 8) : Decidable (side0 x y v) := inferInstanceAs (Decidable (_ = true))
def color1 (v : Fin 8) : Fin 3 := ![0, 1, 0, 1, 2, 0, 2, 0] v
def cut1 (x y : Fin 8) (v : Fin 8) : Prop := (![0, 28, 18, 34, 6, 2, 34, 34, 28, 0, 17, 1, 12, 9, 9, 9, 18, 17, 0, 3, 3, 3, 3, 3, 34, 1, 3, 0, 3, 65, 32, 96, 6, 12, 3, 3, 0, 3, 3, 3, 2, 9, 3, 65, 3, 0, 136, 64, 34, 9, 3, 32, 3, 136, 0, 32, 34, 9, 3, 96, 3, 64, 32, 0] : Fin 64 → Nat) ⟨x.val * 8 + y.val, by omega⟩ |> fun z => z.testBit v.val = true
def side1 (x y : Fin 8) (v : Fin 8) : Prop := (![0, 225, 233, 21, 233, 21, 21, 21, 2, 0, 234, 22, 2, 22, 22, 22, 4, 4, 0, 20, 4, 20, 20, 20, 200, 232, 232, 0, 232, 30, 31, 31, 16, 241, 16, 20, 0, 20, 20, 20, 232, 224, 232, 160, 232, 0, 55, 63, 200, 224, 232, 192, 232, 64, 0, 95, 200, 224, 232, 128, 232, 128, 128, 0] : Fin 64 → Nat) ⟨x.val * 8 + y.val, by omega⟩ |> fun z => z.testBit v.val = true
instance (x y : Fin 8) (v : Fin 8) : Decidable (cut1 x y v) := inferInstanceAs (Decidable (_ = true))
instance (x y : Fin 8) (v : Fin 8) : Decidable (side1 x y v) := inferInstanceAs (Decidable (_ = true))
end Rainbow
