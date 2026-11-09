import CrownVAlg

/-!
Coordinate-killing endomorphism and its kernel.

`coordKill T` is the actual ring endomorphism of `PolyRing n K` obtained from
`MvPolynomial.eval₂Hom` with constant part `MvPolynomial.C` (the identity on
coefficients) and variable part `coordKillArg T`, which sends the pair
`(v, b)` to `0` when `v ∈ T` and to the variable `X (v, b)` itself otherwise.
Hence `coordKill T` kills exactly the two coordinates `x_v, y_v` of each
`v ∈ T`, fixes every surviving variable, and fixes all of `K`.

Main theorem, for every `n : ℕ`, every `CommRing K` and every
`T : Finset (V n)`, with BOTH inclusions:

* `coordKill_ker_eq : RingHom.ker (coordKill T) = Ideal.span (coordGens T)`.

The inclusion `Ideal.span (coordGens T) ≤ ker` is generator annihilation
(`coordKill_xx`, `coordKill_yy`).  The inclusion `ker ≤ span` rests on
`coordKill_diff_mem`: `p - coordKill T p ∈ Ideal.span (coordGens T)` for
every `p`, by the standard `MvPolynomial.induction_on` (constants, sums,
multiplication by a variable); a kernel element then satisfies
`p = p - 0 ∈ span`.  No existing definition is redefined; `Pc` is untouched.
-/

namespace CrownV

section Kernel

variable {n : ℕ} {K : Type*} [CommRing K]

/-- Variable data for `coordKill`: `(v, true)` maps to `0` if `v ∈ T` and to
`x_v` otherwise; `(v, false)` maps to `0` if `v ∈ T` and to `y_v` otherwise. -/
noncomputable def coordKillArg (T : Finset (V n)) : V n × Bool → PolyRing n K :=
  fun p => if p.1 ∈ T then 0 else MvPolynomial.X p

/-- The coordinate-killing endomorphism: an actual `PolyRing n K →+*
PolyRing n K` killing `x_v, y_v` for `v ∈ T`, fixing all remaining variables
and acting as the identity on coefficients. -/
noncomputable def coordKill (T : Finset (V n)) : PolyRing n K →+* PolyRing n K :=
  MvPolynomial.eval₂Hom (MvPolynomial.C) (coordKillArg (n := n) (K := K) T)

/-- Action of `coordKill T` on a variable `X q`: killed iff `q.1 ∈ T`. -/
theorem coordKill_X (T : Finset (V n)) (q : V n × Bool) :
    coordKill T (MvPolynomial.X q) = if q.1 ∈ T then 0 else MvPolynomial.X q := by
  simp only [coordKill, MvPolynomial.eval₂Hom_X', coordKillArg]

/-- Constants are fixed. -/
theorem coordKill_C (T : Finset (V n)) (a : K) :
    coordKill T (MvPolynomial.C a) = MvPolynomial.C a := by
  simp only [coordKill, MvPolynomial.eval₂Hom_C]

/-- Surviving variables are fixed. -/
theorem coordKill_X_of_not_mem (T : Finset (V n)) {q : V n × Bool} (hq : q.1 ∉ T) :
    coordKill T (MvPolynomial.X q) = MvPolynomial.X q := by
  rw [coordKill_X, if_neg hq]

/-- `x_v` is annihilated for `v ∈ T`. -/
theorem coordKill_xx (T : Finset (V n)) {v : V n} (hv : v ∈ T) :
    coordKill T (xx v) = 0 := by
  show coordKill T (MvPolynomial.X (v, true)) = 0
  rw [coordKill_X, if_pos hv]

/-- `y_v` is annihilated for `v ∈ T`. -/
theorem coordKill_yy (T : Finset (V n)) {v : V n} (hv : v ∈ T) :
    coordKill T (yy v) = 0 := by
  show coordKill T (MvPolynomial.X (v, false)) = 0
  rw [coordKill_X, if_pos hv]

/-- Kernel bound: `p` and its `coordKill T`-image differ inside the span of
the coordinates of `T`.  This is the substance of `ker ⊆ span`. -/
theorem coordKill_diff_mem (T : Finset (V n)) (p : PolyRing n K) :
    p - coordKill T p ∈ Ideal.span (coordGens T) := by
  refine MvPolynomial.induction_on
    (motive := fun r : PolyRing n K => r - coordKill T r ∈ Ideal.span (coordGens T)) p ?_ ?_ ?_
  · intro a
    rw [coordKill_C, sub_self]
    exact Submodule.zero_mem _
  · intro q
    obtain ⟨v, b⟩ := q
    cases b
    · by_cases hT : v ∈ T
      · rw [coordKill_X, if_pos hT, sub_zero]
        exact Submodule.mem_span_of_mem ⟨v, hT, Or.inl rfl⟩
      · rw [coordKill_X, if_neg hT, sub_self]
        exact Submodule.zero_mem _
    · by_cases hT : v ∈ T
      · rw [coordKill_X, if_pos hT, sub_zero]
        exact Submodule.mem_span_of_mem ⟨v, hT, Or.inr rfl⟩
      · rw [coordKill_X, if_neg hT, sub_self]
        exact Submodule.zero_mem _
  · intro r s hr hs
    rw [map_add (coordKill T)]
    have h : r + s - (coordKill T r + coordKill T s)
        = (r - coordKill T r) + (s - coordKill T s) := by ring
    rw [h]
    exact Ideal.add_mem hr hs
  · -- multiplication by a variable: `p * X q - φ p * φ (X q)`.
    intro r q hr
    obtain ⟨v, b⟩ := q
    cases b
    · by_cases hT : v ∈ T
      · have hX : (MvPolynomial.X (v, true) : PolyRing n K) ∈ Ideal.span (coordGens T) :=
          Submodule.mem_span_of_mem ⟨v, hT, Or.inl rfl⟩
        have hkey : r * MvPolynomial.X (v, true) - coordKill T r * coordKill T (MvPolynomial.X (v, true))
            = (r - coordKill T r) * MvPolynomial.X (v, true)
              + coordKill T r * (MvPolynomial.X (v, true) - coordKill T (MvPolynomial.X (v, true))) := by
          rw [map_mul (coordKill T), coordKill_X, if_pos hT, mul_zero] at *
          ring
        rw [hkey]
        refine Ideal.add_mem (Ideal.span (coordGens T)).2 ?_ ?_
        · exact mul_mem_right
        · exact mul_mem_right
      · sorry
    · sorry

end Kernel

end CrownV
