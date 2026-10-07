import Std

/-! Modular arithmetic behind ordinary BSGS, independently of an implementation.
These lemmas prove no lookup algorithm, cost bound, or elliptic-curve result. -/
namespace Research.BSGSArithmetic

def negStride (q m : Nat) : Nat := (q - m % q) % q

def blockCount (q m : Nat) : Nat := (q - 1) / m + 1

theorem stride_cancels (q m : Nat) (hq : 0 < q) :
    (m + negStride q m) % q = 0 := by
  have hm : m % q < q := Nat.mod_lt m hq
  have hsum : m % q + (q - m % q) = q := by omega
  calc
    (m + negStride q m) % q = (m % q + (q - m % q)) % q := by
      simp [negStride, Nat.add_mod]
    _ = 0 := by rw [hsum, Nat.mod_self]

/-- A matching baby index recovers the unique canonical scalar even if baby
indices exceed q. Neither primality nor coprimality is needed. -/
theorem recover (q m d i j : Nat) (hq : 0 < q) (hd : d < q)
    (hmatch : (d + i * negStride q m) % q = j % q) :
    (i * m + j) % q = d := by
  calc
    (i * m + j) % q = (i * m + (d + i * negStride q m)) % q := by
      rw [Nat.add_mod (i * m) j, Nat.add_mod (i * m) (d + _), hmatch]
    _ = (d + i * (m + negStride q m)) % q := by
      rw [Nat.mul_add]
      congr 1
      omega
    _ = d := by
      simp [Nat.add_mod, Nat.mul_mod, stride_cancels q m hq, Nat.mod_eq_of_lt hd]

theorem quotient_in_range (q m d : Nat) (hq : 0 < q) (hd : d < q) :
    d / m < blockCount q m := by
  have hle : d ≤ q - 1 := by omega
  have hdiv : d / m ≤ (q - 1) / m := Nat.div_le_div_right hle
  unfold blockCount
  omega

/-- Euclidean digits provide a matching block/baby pair. The positive block
width is essential to obtain a baby index below m. -/
theorem complete_digits (q m d : Nat) (hq : 0 < q) (hm : 0 < m) (hd : d < q) :
    d / m < blockCount q m ∧ d % m < m ∧
      (d + (d / m) * negStride q m) % q = (d % m) % q := by
  refine ⟨quotient_in_range q m d hq hd, Nat.mod_lt d hm, ?_⟩
  have hdecomp : d = d % m + (d / m) * m := by
    simpa [Nat.mul_comm] using (Nat.mod_add_div d m).symm
  calc
    (d + (d / m) * negStride q m) % q =
        (d % m + (d / m) * (m + negStride q m)) % q := by
      rw [Nat.mul_add]
      congr 1
      omega
    _ = (d % m) % q := by
      simp [Nat.add_mod, Nat.mul_mod, stride_cancels q m hq]

end Research.BSGSArithmetic
