/-
# Bunkbed E7 (r20): the fresh-token split

Tokens first seen when the window grows from `m` to `m+1`, the extension map
`Asg n m × (Fresh → Bool) → Asg n (m+1)`, and the bijection
`Asg n (m+1) ≃ Asg n m × (Fresh n m → Bool)`.  Pure finite combinatorics.
-/
import BunkbedBase
import BunState
import BunBridge
import BunUpperSupport
import BunReachSupport
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

namespace Bun

open Finset

/-! ### Finite window instances -/

instance winFintype {n m : Nat} : Fintype (Win n m) :=
  Subtype.fintype (fun t : Token n => tmax t ≤ m)

noncomputable instance asgFintype {n m : Nat} : Fintype (Asg n m) := by
  unfold Asg
  exact Fintype.ofFinite _

/-! ### Fresh tokens of level `m+1` -/

/-- Tokens whose `tmax` is exactly `m+1`: the ones first seen at the window `m+1`. -/
def Fresh (n m : Nat) := {t : Win n (m+1) // ¬ tmax t.1 ≤ m}

instance freshFintype {n m : Nat} : Fintype (Fresh n m) :=
  Subtype.fintype (fun t : Win n (m+1) => ¬ tmax t.1 ≤ m)

theorem tmax_fresH {n m : Nat} (hm : m < n) (i : Nat) (hic : i < m) (l : Bool) :
    tmax (fresH (n := n) (m := m) hm i hic l).1 = m := by
  simp only [fresH]
  exact tmax_htok _ _ _ _

theorem tmax_fresV {n m : Nat} (hm : m < n) :
    tmax (fresV (n := n) (m := m) hm).1 = m := by
  simp only [fresV]
  exact tmax_vtok _

/-- The fresh horizontal token `(k,m+1,l)` as an element of `Fresh n m`. -/
def freshHAt {n m : Nat} (hm : m+1 < n) (k : Nat) (hk : k < m+1) (l : Bool) : Fresh n m :=
  ⟨fresH (n := n) (m := m+1) hm k hk l, by
    have h := tmax_fresH (n := n) (m := m+1) hm k hk l
    omega⟩

/-- The fresh vertical token `m+1` as an element of `Fresh n m`. -/
def freshVAt {n m : Nat} (hm : m+1 < n) : Fresh n m :=
  ⟨fresV (n := n) (m := m+1) hm, by
    have h := tmax_fresV (n := n) (m := m+1) hm
    omega⟩

theorem freshHAt_val {n m : Nat} (hm : m+1 < n) (k : Nat) (hk : k < m+1) (l : Bool) :
    (freshHAt hm k hk l).1 = fresH (n := n) (m := m+1) hm k hk l := rfl

theorem freshVAt_val {n m : Nat} (hm : m+1 < n) :
    (freshVAt (n := n) (m := m) hm).1 = fresV (n := n) (m := m+1) hm := rfl

/-! ### Extension -/

/-- Extend a `m`-window assignment by arbitrary bits on the fresh tokens. -/
def ext {n m : Nat} (w : Asg n m) (f : Fresh n m → Bool) : Asg n (m+1) :=
  fun t => if h : tmax t.1 ≤ m then w ⟨t.1, h⟩ else f ⟨t, h⟩

theorem ext_old {n m : Nat} (w : Asg n m) (f : Fresh n m → Bool) (t : Win n m) :
    ext w f ⟨t.1, Nat.le_trans t.2 (Nat.le_succ m)⟩ = w t := by
  have h : tmax t.1 ≤ m := t.2
  simp only [ext]
  rw [dite_eq_left h]
  exact congrArg w (Subtype.ext rfl)

theorem ext_fresh {n m : Nat} (w : Asg n m) (f : Fresh n m → Bool) (g : Fresh n m) :
    ext w f g.1 = f g := by
  have h : ¬ tmax g.1.1 ≤ m := g.2
  simp only [ext]
  rw [dite_eq_right h]
  exact congrArg f (Subtype.ext rfl)

theorem res_ext {n m : Nat} (w : Asg n m) (f : Fresh n m → Bool) :
    res n m (ext w f) = w := by
  funext t
  simp only [res]
  exact ext_old w f t

theorem ext_res {n m : Nat} (w : Asg n (m+1)) :
    ext (res n m w) (fun f => w f.1) = w := by
  funext t
  have ht : tmax t.1 ≤ m+1 := t.2
  by_cases hm : tmax t.1 ≤ m
  · simp only [ext]
    rw [dite_eq_left hm]
    show res n m w ⟨t.1, hm⟩ = w t
    simp only [res]
    exact congrArg w (Subtype.ext rfl)
  · simp only [ext]
    rw [dite_eq_right hm]

/-! ### The window split -/

/-- A `(m+1)`-window assignment is exactly a `m`-window assignment together with
arbitrary fresh bits. -/
def asgSuccEquiv (n m : Nat) : Asg n (m+1) ≃ Asg n m × (Fresh n m → Bool) where
  toFun w := (res n m w, fun f => w f.1)
  invFun p := ext p.1 p.2
  left_inv w := ext_res w
  right_inv p := by
    obtain ⟨w, f⟩ := p
    refine Prod.ext (res_ext w f) ?_
    funext g
    exact ext_fresh w f g

/-- The window split as a cardinality recursion. -/
theorem card_asg_succ (n m : Nat) :
    Fintype.card (Asg n (m+1)) = Fintype.card (Asg n m) * 2 ^ Fintype.card (Fresh n m) := by
  classical
  rw [Fintype.card_congr (asgSuccEquiv n m), Fintype.card_prod, Fintype.card_fun]
  simp [Fintype.card_bool]

end Bun
