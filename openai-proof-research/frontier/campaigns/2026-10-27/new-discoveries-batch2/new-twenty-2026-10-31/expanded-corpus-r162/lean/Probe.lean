import Mathlib.Data.Nat.Totient
import Mathlib.Tactic
example : Nat.totient 16384 = 8192 := by
  have h : Nat.Prime 2 := by norm_num
  have e : 16384 = 2^14 := by norm_num
  rw [e, Nat.totient_prime_pow h (by norm_num)]
  norm_num
#print Nat.totient_prime_pow
#print Nat.totient_prime
#print Equiv.ofBijective
