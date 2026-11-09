import CrownVCoordPrime
import CrownVFullSide

/-! # CrownV fullside primality (r18)

The fullside ideals of the original `CrownVAlg.Pc` are prime: by the frozen
span equalities `CrownV.pcXside_eq_span` / `CrownV.pcYside_eq_span` each is
literally the coordinate span whose primality is `CrownV.coordSpan_isPrime`.
The `Pc` definition is used unchanged; no primality is assumed. -/

namespace CrownV

/-- The fullside X ideal `Pc (Xside n)` is prime for every `n` and field `K`. -/
theorem pcXside_isPrime (n : Nat) (K : Type*) [Field K] :
    Ideal.IsPrime (Pc (n := n) (K := K) (Xside n)) := by
  have h := pcXside_eq_span (n := n) (K := K)
  rw [h]
  exact coordSpan_isPrime n K (Xside n)

/-- The fullside Y ideal `Pc (Yside n)` is prime for every `n` and field `K`. -/
theorem pcYside_isPrime (n : Nat) (K : Type*) [Field K] :
    Ideal.IsPrime (Pc (n := n) (K := K) (Yside n)) := by
  have h := pcYside_eq_span (n := n) (K := K)
  rw [h]
  exact coordSpan_isPrime n K (Yside n)

end CrownV
