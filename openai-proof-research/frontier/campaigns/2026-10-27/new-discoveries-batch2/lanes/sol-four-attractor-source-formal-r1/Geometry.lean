import Mathlib.Data.Nat.Find
set_option autoImplicit false
set_option warningAsError true
namespace FourAttractor
def inI (x l r : Nat) : Prop := l ≤ x ∧ x ≤ r
def hit (a b c d l r : Nat) : Prop := inI a l r ∨ inI b l r ∨ inI c l r ∨ inI d l r
def hitTwo (a b c d l r s t : Nat) : Prop := hit a b c d l r ∨ hit a b c d s t
set_option maxHeartbeats 2000000 in
theorem obstruction (a b c d : Nat)
    (h1 : hit a b c d 5 10) (h2 : hit a b c d 6 11) (h3 : hit a b c d 7 12)
    (h4 : hit a b c d 13 18) (h5 : hit a b c d 15 20) (h6 : hit a b c d 17 22)
    (h7 : hit a b c d 23 28) (h8 : hit a b c d 24 29) (h9 : hit a b c d 25 30)
    (h10 : hitTwo a b c d 3 6 11 14) (h11 : hitTwo a b c d 21 24 29 32) : False := by
  unfold hitTwo hit inI at *
  omega
end FourAttractor
