# Literal endpoint remains unproved — zero credit

The checked identity `mixed_layercake` gives the actual mixed moment as the actual positive-orthant threshold integral. `prefix_gap_integral` evaluates the proposed gap integral and `gap_integrable` proves that integral is genuine. No checked theorem yet equates these two integrals.

The central remaining theorem, with NO hypotheses of integrability or moments, is:

```lean
∀ {n L d : ℕ} (hL : 0 < L) (e : Fin d → Edge n L),
  (∫ ω, ∏ i, lifetime hL (e i) ω ∂clockMeasure n) = symCoefficient e
```

A sufficient next analytic bridge is:

```lean
∀ {n L d : ℕ} (hL : 0 < L) (e : Fin d → Edge n L),
  (∫⁻ t : Fin d → ℝ in Set.pi Set.univ (fun _ => Set.Ioi (0 : ℝ)),
    ENNReal.ofReal (Real.exp (-∑ v, vertexThreshold e t v))) =
      ENNReal.ofReal (symCoefficient e)
```

To prove it on the ordinary route:

1. Prove volume-null ties `{t | t i = t j}` for i ≠ j; zero coordinates are checked in `volume_coordinates_nonzero`. Partition the complement into all labelled descending chambers, indexed by `Equiv.Perm (Fin d)`. Edge coincidences never quotient this index.
2. Construct the linear descending-gap map and inverse `t (σ i) = ∑ j ≥ i, u j`. Establish inverse identities, determinant of absolute value 1, and positive-orthant/chamber domain transport. No gap substitution or determinant theorem is claimed in this packet.
3. Prove `∑ v, vertexThreshold e t v = ∑ j, (prefixUnion (tuplePerm σ e) j).card * u j` under that map. Orientation is prefix, not suffix unions: a vertex first appearing at k contributes every gap j ≥ k.
4. Transport each chamber integral and apply the checked `prefix_gap_integral`, then sum over all permutations. This is the substantial unresolved formalization, not merely import wiring.
5. Use `mixed_layercake`, nonnegative mixed products and finite `symCoefficient` to return to real integrals. Integrability of arbitrary mixed-product powers is already checked; no such assumption remains.
6. Substitute the concrete identity into checked `integrated_expansion` and `symmetrized_sum` to obtain the actual factorial identity for every real weight vector. Then checked `concrete_integral_convex`, positivity of d!, and restriction to the sum-one simplex give `SourceConjecture`. The assembly and literal endpoint are still unproved.

The all-same-edge control d!/L^d is also not a checked theorem here; the scalar clock moment is k!, and the source repeated-edge coefficient L^(-d) is checked. They must not be conflated.

These displayed residuals are specifications in prose, not axioms or assumed Lean declarations. No theorem `SourceConjecture` is inhabited, and no helper credit or acceptance is requested.
