import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Decide
import Mathlib.Tactic.Omega
set_option autoImplicit false
set_option warningAsError true
namespace EdgeIrregulator
-- Bit order: ab,ac,ad,bc,bd,cx,xy,yh. True means retained.
def bit (r : Fin 8 → Bool) (k : Fin 8) : ℕ := if r k then 1 else 0
def da (r : Fin 8 → Bool) : ℕ := bit r 0 + bit r 1 + bit r 2
def db (r : Fin 8 → Bool) : ℕ := bit r 0 + bit r 3 + bit r 4
def dc (r : Fin 8 → Bool) : ℕ := bit r 1 + bit r 3 + bit r 5
def dd (r : Fin 8 → Bool) : ℕ := bit r 2 + bit r 4
def dx (r : Fin 8 → Bool) : ℕ := bit r 5 + bit r 6
def dy (r : Fin 8 → Bool) : ℕ := bit r 6 + bit r 7
def DiamondOK (r : Fin 8 → Bool) : Prop :=
  (r 0 = true → da r ≠ db r) ∧ (r 1 = true → da r ≠ dc r) ∧
  (r 2 = true → da r ≠ dd r) ∧ (r 3 = true → db r ≠ dc r) ∧
  (r 4 = true → db r ≠ dd r)
def diamondCost (r : Fin 8 → Bool) : ℕ :=
  (1-bit r 0)+(1-bit r 1)+(1-bit r 2)+(1-bit r 3)+(1-bit r 4)
def pathCost (r : Fin 8 → Bool) : ℕ := (1-bit r 5)+(1-bit r 6)+(1-bit r 7)
-- Closed 256-state certificates, reduced by the kernel, independent of hub degree.
theorem diamond_boundary_certificate : ∀ r : Fin 8 → Bool, DiamondOK r → 2 ≤ diamondCost r := by
  decide +kernel
theorem path_boundary_certificate : ∀ r : Fin 8 → Bool,
    (r 6 = true → dx r ≠ dy r) → 1 ≤ pathCost r := by
  decide +kernel
theorem block_boundary_certificate (r : Fin 8 → Bool) (h : DiamondOK r)
    (hxy : r 6 = true → dx r ≠ dy r) : 3 ≤ diamondCost r + pathCost r := by
  have := diamond_boundary_certificate r h
  have := path_boundary_certificate r hxy
  omega
end EdgeIrregulator
