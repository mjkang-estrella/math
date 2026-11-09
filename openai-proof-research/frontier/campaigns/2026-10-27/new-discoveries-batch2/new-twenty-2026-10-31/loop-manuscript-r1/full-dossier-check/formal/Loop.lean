import Mathlib.Data.Fintype.Prod
import Mathlib.Basic.ExistsUnique
import Mathlib.Data.Finset.Card

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Loop380362
abbrev Q := Bool × Bool × Bool × Bool
def zero : Q := (false, false, false, false)
def group (x y : Q) : Q :=
 (xor x.1 y.1, xor x.2.1 y.2.1, xor x.2.2.1 y.2.2.1, xor x.2.2.2 y.2.2.2)
def factor (x y : Q) : Bool :=
 xor (xor (x.1 && x.2.1 && y.2.2.1) (x.1 && y.2.1 && x.2.2.1))
 (y.1 && x.2.1 && x.2.2.1)
def loop (x y : Q) : Q :=
 (xor x.1 y.1, xor x.2.1 y.2.1, xor x.2.2.1 y.2.2.1,
 xor (xor x.2.2.2 y.2.2.2) (factor x y))
def IsMoufangLoop {α : Type} (one : α) (mul : α → α → α) : Prop :=
 (∀ x, mul one x = x ∧ mul x one = x) ∧
 (∀ a b, ∃! x, mul a x = b) ∧
 (∀ a b, ∃! x, mul x a = b) ∧
 (∀ x y z, mul (mul (mul x y) x) z = mul x (mul y (mul x z)))
def leftDiv (a b : Q) : Q :=
 let q := group a b
 (q.1, q.2.1, q.2.2.1, xor q.2.2.2 (factor a q))
def rightDiv (a b : Q) : Q :=
 let q := group a b
 (q.1, q.2.1, q.2.2.1, xor q.2.2.2 (factor q a))
theorem group_loop : IsMoufangLoop zero group := by
 have hl : ∀ a b, group a (group a b) = b := by decide
 have hr : ∀ a b, group (group a b) a = b := by decide
 have il : ∀ a x y, group a x = group a y → x = y := by decide
 have ir : ∀ a x y, group x a = group y a → x = y := by decide
 refine ⟨by decide, ?_, ?_, by decide⟩
 · intro a b; exact ⟨group a b, hl a b, fun y hy => il a y _ (hy.trans (hl a b).symm)⟩
 · intro a b; exact ⟨group a b, hr a b, fun y hy => ir a y _ (hy.trans (hr a b).symm)⟩
theorem code_loop : IsMoufangLoop zero loop := by
 have hl : ∀ a b, loop a (leftDiv a b) = b := by decide
 have hr : ∀ a b, loop (rightDiv a b) a = b := by decide
 have il : ∀ a x y, loop a x = loop a y → x = y := by decide
 have ir : ∀ a x y, loop x a = loop y a → x = y := by decide
 refine ⟨by decide, ?_, ?_, by decide⟩
 · intro a b; exact ⟨leftDiv a b, hl a b, fun y hy => il a y _ (hy.trans (hl a b).symm)⟩
 · intro a b; exact ⟨rightDiv a b, hr a b, fun y hy => ir a y _ (hy.trans (hr a b).symm)⟩
theorem group_associative : ∀ x y z, group (group x y) z = group x (group y z) := by decide
theorem not_associative : ¬ ∀ x y z, loop (loop x y) z = loop x (loop y z) := by decide
def distance : Nat := (Finset.univ.filter (fun p : Q × Q => group p.1 p.2 ≠ loop p.1 p.2)).card
theorem distance_eq : distance = 64 := by decide
theorem order_eq : Fintype.card Q = 16 := by decide

def assocGroup (_x _y _z : Q) : Q := zero
def assocLoop (x y z : Q) : Q := group (loop (loop x y) z) (loop x (loop y z))
def IsAssociator {α : Type} (mul : α → α → α) (a : α → α → α → α) : Prop :=
 ∀ x y z, mul (mul x (mul y z)) (a x y z) = mul (mul x y) z
def EquivalentAssociators {α : Type} (one : α) (a b : α → α → α → α) : Prop :=
 ∃ e : α ≃ α, e one = one ∧ ∀ x y z, e (a x y z) = b (e x) (e y) (e z)
theorem group_assoc_spec : IsAssociator group assocGroup := by unfold IsAssociator; decide
theorem loop_assoc_spec : IsAssociator loop assocLoop := by unfold IsAssociator; decide
def u : Q := (true, false, false, false)
def v : Q := (false, true, false, false)
def w : Q := (false, false, true, false)
theorem assoc_nonzero : assocLoop u v w ≠ zero := by decide
theorem nonequivalent : ¬ EquivalentAssociators zero assocGroup assocLoop := by
 rintro ⟨e, he, ha⟩
 have h := ha (e.symm u) (e.symm v) (e.symm w)
 change e zero = _ at h
 rw [he, e.apply_symm_apply, e.apply_symm_apply, e.apply_symm_apply] at h
 exact assoc_nonzero h.symm

def SourceClaim : Prop := ∀ (α : Type) [Fintype α] [DecidableEq α]
 (one : α) (mul₁ mul₂ : α → α → α) (a₁ a₂ : α → α → α → α),
 IsMoufangLoop one mul₁ → IsMoufangLoop one mul₂ →
 IsAssociator mul₁ a₁ → IsAssociator mul₂ a₂ →
 ¬ EquivalentAssociators one a₁ a₂ →
 3 * (Fintype.card α)^2 ≤ 8 * (Finset.univ.filter
 (fun p : α × α => mul₁ p.1 p.2 ≠ mul₂ p.1 p.2)).card

theorem source_refutation : ¬ SourceClaim := by
 intro h
 have hb := h Q zero group loop assocGroup assocLoop group_loop code_loop
   group_assoc_spec loop_assoc_spec nonequivalent
 change 3 * (Fintype.card Q)^2 ≤ 8 * distance at hb
 rw [distance_eq, order_eq] at hb
 exact (by decide : ¬ (3 * 16^2 ≤ 8 * 64)) hb
end Loop380362
