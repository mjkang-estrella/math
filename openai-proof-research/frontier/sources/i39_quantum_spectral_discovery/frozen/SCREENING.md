# Candidate screening and unresolved research questions

Only `findings/F*.md` are accepted deliverables. `proposals/` preserves raw
research reports, including claims later corrected or rejected. An agent's
initial “proved” label is not a substitute for the final disposition here.
All mathematical statements are evaluated under the user's assumption that
the pinned OpenAI theorems are true. Literature priority remains separate.

## Promoted candidates

The index in [README.md](README.md) links each complete statement, proof,
independent review and separate commit. The proof hypotheses were:

- **F001:** use the generalized Flint–Hills series as the squared norm of a
  Fourier inverse; telescope to obtain sharp quadrature regularity.
- **F002:** split at an optimized degree threshold; combine the new degree
  coloring theorem with classical Ramsey bounds and a critical-subgraph
  genus reduction.
- **F003:** encode quadratic solvability in the singular points of
  `uv = Σ q_i(x)² + t⁴`, while preserving rationality and normality.
- **F004:** scale the cylinder coordinate in the accepted cancellation
  example; transport the action to affine space and inspect fixed schemes.
- **F005:** encode finite-versus-infinite c.e. sets by reciprocal-mass blocks;
  single-fold representation preserves multiplicity-free summation after
  degree reduction.
- **F006:** apply the same representation to separated base-four halting
  digits; recover the halting set from the resulting convergent sum.
- **F007:** apply the gap inequality to an exponential of a conserved block
  charge; only boundary bonds remain in the double commutator.
- **F008:** approximate the power-free indicator by fixed periodic sieves;
  binary Elliott cancellation survives the average-error limit.
- **F009:** discard negligible repeated-prime mass, mark PD atoms with four
  colors, and couple those colors to two uniform divisors.
- **F010:** use polynomial partitioning at degree approximately `m/n` to
  extend the balanced unit-distance estimate to unequal set sizes.

## Correct but not promoted as additional findings

| Candidate | Disposition |
|---|---|
| Infimum one-derivative loss for the π rotation | Equivalent reformulation of μ(π)=2; reviewed supporting note for F001. |
| Quadratic arithmetic cost for graph inverse updates on more than n^0.465 hubs | Classical Woodbury framework with new rectangular exponent; scout proof and finite algebra checks, no separate adversarial review. No bit-complexity claim. |
| Infinite matrix units and zero-class projective modules in the new group algebra | Classical one-sided-inverse algebra mechanism; scout proof only, lower novelty value. |
| Anderson point-source transport T^(p/d) at fixed weak disorder | Detailed scout proof of classical spectral/transport transfer; not independently promoted. Does not imply diffusion. |
| Good minimal models for the stated compact Kähler fourfold category | Partial cross-family report recovered after provider failure; hypothesis matching is not independently reviewed or promoted. |
| Simultaneous primitive roots for prime bases | Cross-family scout did not discharge its marked Type-II premise; unproved here. |
| Bounded nonconvex perturbations of the new log-Sobolev class | Standard Holley–Stroock transfer; not a new general method. |
| Curved-region density ½ log²(1/t) for consecutive largest factors | Elementary pushforward of the new joint law; scout proof only. Finite data have substantial bias. |
| Rational-phase sine-series convergence criterion | Scout proof; classical congruence approximation mechanism and unresolved priority. |
| Inverse-sine moment asymptotics and logarithmic endpoint for 0<b<1 | Scout proof; not independently promoted. No b=1 assertion. |
| Multicolor cycle–clique Ramsey identity in the enlarged range | Classical color-merging/blowup proof; much of the range already in literature. Scout checks only. |
| Clique-free chromatic logarithmic exponent from Ramsey bounds | Standard translation; no separate new mechanism. |

## Duplicates rejected by manuscript inspection

- Generalized unshifted Flint–Hills convergence: already `series:generalized`.
- Quartic/sum-of-quadratic-squares H10(Q): already `thm:degree-normal-form`.
- Simultaneous polynomial power-free densities: already `cor:separable-products`.
- Largest-prime-factor ordering density one half: already `cor:comparison`.
- Van der Waerden color bounds and weighted/dense-prime progression
  consequences: already in the arithmetic-progression companions.
- Borsuk counterexamples in every dimension at least nine: already
  `cor:higher-dimensions`.
- Smooth zero-entropy and all-orders mixing consequences: already in the
  simple-Lebesgue-spectrum manuscript.
- Stable-coordinate and affine-fibration cancellation corollaries: already
  in the cancellation manuscript.
- Polylogarithmic least quadratic nonresidues and deterministic modular
  square roots: already in the zero-free-region manuscript.

## Invalid or unjustified upgrades rejected

- **Unbalanced-incidence scout, optional A1 prose:** its two decay exponents
  lie on opposite sides of three; “both improve three” was false.
- **Optional A3 comparison:** `O(k^(2/3)n^(4/3))` is not a uniform bound for
  arbitrary k prescribed distances. The square-grid counterexample is in
  the incidence review. This comparator and its claimed crossover are removed.
- **Variable β=1+o(1):** cannot be inserted into a fixed-exponent theorem
  with uncontrolled constants; the upstream source also records a
  fixed-power superlinear unit-distance lower bound.
- **List/DP extension of F002:** independent-set removal and disjoint
  ordinary palettes do not prove the corresponding list/DP statement.
- **Projectivizing F003:** creates a rational singular point at infinity
  on every input, destroying the intended decision reduction.
- **Unique witnesses over Z or Q:** not supplied by the natural-number
  single-fold theorem; sign and sum-of-squares encodings introduce multiplicity.
- **π irrationality exponent two ⇒ bounded partial quotients:** false as
  a general implication; the exact one-derivative endpoint stays unresolved.
- **Arbitrary real sine phases:** homogeneous approximation control does
  not give every inhomogeneous target a uniform lower bound.
- **Every-scale logarithmic savings in F008:** a moving sieve cutoff would
  require unavailable uniformity in affine coefficients and large-prime tails.
- **Absolute continuity ⇒ diffusion:** the transport mechanism only gives
  the stated lower exponent, not diffusive growth or conductivity.
- **Mixing of all orders ⇒ a central limit theorem:** quantitative input
  is missing.
- **Primitive-root dyadic lower counts ⇒ divergent prime reciprocal sum:**
  the resulting lower bounds behave like a convergent sum of inverse squares.

## Follow-up hypotheses, deliberately not validated here

1. **Quantitative prime-predecessor divisor laws.** A rate in an appropriate
   full-mass metric for the upstream PD law should transfer to the divisor
   law, combined with the explicit repeated-prime estimate. The missing
   premise is a usable PD rate; finite sieve trends do not supply it.
2. **An effective rate for quartic-conditioned signs.** Uniform binary
   cancellation up to growing sieve moduli, plus a quantitative large-prime
   square-divisor estimate, could give a rate. Fixed-coefficient results
   alone do not justify this.
3. **Sharper dependence on the number of radii.** Summing F010 over radii
   gives a factor k. Improving that factor requires controlling incidences
   shared across radii; the false comparator above is not a starting theorem.
4. **Better spin-tail constants or a larger moment domain.** The double
   commutator uses a worst-case operator norm. Sharper ground-state control
   might improve it, but a Gaussian tail for all deviations does not follow
   from the finite interval of exponential moments proved here.
5. **Literature priority.** Search specifically for prior conditional forms
   of the new arithmetic and geometric specializations, and obtain the
   full Gimbel–Thomassen text before claiming the edge/genus consequence was
   never previously formulated.

These are research directions with explicit missing premises, not additional
claimed theorems. No unresolved step in them is used by the accepted findings.
