import Mathlib.Data.Nat.Basic

set_option autoImplicit false
set_option warningAsError true

namespace CascadeRate

def depth : ℕ → ℕ
  | 0 => 0
  | k + 1 => (k + 1) ^ 2 * (depth k + (k + 1) + 10)

def anchorLength (k : ℕ) : ℕ := 2 * k + 2
def terminalLength (k : ℕ) : ℕ := depth (k - 1) + 3
def remainderLength (k : ℕ) : ℕ := depth k - anchorLength k - terminalLength k
def blockCount (k : ℕ) : ℕ := remainderLength k / k
def tailRemainder (k : ℕ) : ℕ := remainderLength k % k
def freeCount (k : ℕ) : ℕ := (k - 2) * blockCount k
def deficit (k : ℕ) : ℕ := depth k - 1 - freeCount k

end CascadeRate
