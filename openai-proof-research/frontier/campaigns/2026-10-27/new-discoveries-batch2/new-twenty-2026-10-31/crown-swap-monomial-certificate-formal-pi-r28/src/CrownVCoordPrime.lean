import CrownVCoordKernelEq

/-! # CrownV coordinate-span primality (r18, sealed)

The span of the coordinate generators `CrownV.coordGens T` is a prime ideal of
`PolyRing n K` for every `n`, every field `K` and every `T : Finset (V n)`.
The proof uses only the frozen kernel equality `CrownV.coordKill_ker_eq`
(the actual kernel of the endomorphism `CrownV.coordKill T`) and the integral
domain structure of the polynomial codomain; no new definitions, no quotients. -/

namespace CrownV

/-- A ring homomorphism into an integral domain has prime kernel: the kernel
is proper because `1 ↦ 1 ≠ 0`, and `a * b ↦ 0` splits by domain cancellation. -/
theorem coordKer_isPrime (n : Nat) (K : Type*) [Field K] (T : Finset (V n)) :
    Ideal.IsPrime (RingHom.ker (coordKill (n := n) (K := K) T)) := by
  refine ⟨?_, ?_⟩
  · intro htop
    have h1 : (1 : PolyRing n K) ∈ RingHom.ker (coordKill (n := n) (K := K) T) := by
      rw [htop]
      exact Submodule.mem_top
    have h2 : coordKill (n := n) (K := K) T 1 = 0 := RingHom.mem_ker.mp h1
    exact one_ne_zero ((map_one _).symm.trans h2)
  · intro a b hab
    have h0 : coordKill (n := n) (K := K) T (a * b) = 0 := RingHom.mem_ker.mp hab
    rw [map_mul] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact Or.inl (RingHom.mem_ker.mpr h)
    · exact Or.inr (RingHom.mem_ker.mpr h)

/-- The span of the coordinate generators of any `T : Finset (V n)` over a
field `K` is a prime ideal of `PolyRing n K`. -/
theorem coordSpan_isPrime (n : Nat) (K : Type*) [Field K] (T : Finset (V n)) :
    Ideal.IsPrime (Ideal.span (coordGens (n := n) (K := K) T) : Ideal (PolyRing n K)) := by
  have hker : RingHom.ker (coordKill (n := n) (K := K) T)
      = Ideal.span (coordGens (n := n) (K := K) T) := coordKill_ker_eq (T := T)
  rw [← hker]
  exact coordKer_isPrime n K T

end CrownV
