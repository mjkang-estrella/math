# Frozen scope O217 — fourth-moment universality of zero-field SK fluctuations

Frozen 2026-10-17 after `217-prefreeze-feasibility.md` and `217-prefreeze-comparison.md`, before the full proof is written. Main and variance proof ideas were developed before this freeze and are acknowledged as feasibility work. No prior frozen-proof chronology is claimed.

For every real β>0 and every finite K≥1 there is C=C(β,K)<∞ with the following property. For every integer n≥2 and every independent real family (J_e) indexed by unordered pairs e={i,j}, 1≤i<j≤n, with E J_e=0, E J_e²=1 and E|J_e|⁴≤K, put

F_n(J)=log Σ_(σ∈{−1,1}^n) exp[(β/√n)Σ_(i<j)J_ij σ_iσ_j].

Let g_e be independent standard Gaussians and V_n=Var F_n(g). There is no external field. Then:

(1) |E F_n(J)−E F_n(g)|≤C.

(2) |Var F_n(J)−V_n|≤C(1+√V_n).

(3) For every a≥1, c∈R, and real φ∈C^6(R) with φ and its first six derivatives bounded,

|Eφ((F_n(J)−c)/a)−Eφ((F_n(g)−c)/a)|
 ≤ (C/a) Σ_(k=1)^6 ||φ^(k)||_∞.

The constant is independent of n, the individual coordinate distributions, a,c and φ. The family may be nonidentical, may vary arbitrarily with n, and no joint construction across n is required. No symmetry, zero third moment, tail shape, finite fifth/sixth moment or Gaussian moment matching beyond mean/variance is assumed.

Consequently, for every fixed β>1 and every such triangular array with one finite uniform fourth-moment bound, accepting the pinned Gaussian family217 theorems at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb,

Var F_n(J)/n^(1/3) → a_2(β)>0,
(F_n(J)−E F_n(J))/sqrt(Var F_n(J)) ⇒ ν_β,

where a_2(β) and ν_β are exactly the Gaussian prefactor and standardized law. The denominator is positive for all sufficiently large n; positivity at every finite n is not required and fails for some discrete disorders at n=2. Convergence is through all integers. The model uses its own exact mean and variance. No assertion about all higher moments or exponential moments of non-Gaussian pressure is included; finite fourth moments cannot support such a blanket assertion. No varying β, external field, ground-state, mixed-p-spin, dynamical or multitemperature extension is part of this target.

Supporting formalization, if accepted for later implementation, can cover finite sign-gauge/permutation identities, Taylor-square algebra, combinatorial derivative exponent/cardinality sums and the finite maximum quadratic bootstrap. Full probability/analytic replacement and the source Gaussian theorem would remain in the human proof unless separately formalized. No Lean result is claimed here.

Author Myeongjin Kang, no affiliation. Original prose CC BY 4.0; original code MIT. Source truths stipulated, not audited. This freeze does not grant proof or contribution acceptance or change the campaign count.
