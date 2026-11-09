# Rational critical points refuting MathDB 328705

Candidate only: independent source, novelty/significance and final manuscript review remain for the parent. No count changes.

Hwangrae Lee, arXiv:1409.0684v2 (21 October 2015), equation (2.1), p.4, and Conjecture 2.14, p.7, concern the real critical points on the nonzero affine cone

    sum x_i^d = 0,
    x_i^(d-1)(x_j-u_j) = x_j^(d-1)(x_i-u_i).

The claimed bound is 2n-1 for n+1 coordinates. This is visibly linear in the original page rendering, not a flattened exponential. Section 2.3 discusses odd d and the finite number of real solutions. The normalized MathDB record explicitly quantifies over real u for which there are finitely many critical points. We use this exact scope.

## Construction

Set n=17, d=3, and u_i=2 for all eighteen coordinates. For each two-element subset S of {0,...,17}, define x_i=-2 on S and x_i=1 otherwise. Then

    sum x_i^3 = 16 - 2*8 = 0,
    x_i - 2 = -x_i^2.

The latter identity gives every pairwise critical equation. These are nonzero smooth points: the gradient of the cubic is (3x_i^2), whose entries here are 3 or 12. Distinct subsets give distinct points, so there are at least binomial(18,2)=153 critical points. The observation vector has all entries nonzero and is outside the cone, since its cubic sum is 144. The proposed bound is 33.

These are genuine critical points of squared Euclidean distance: its gradient is 2(x-u)=-2(x_i^2), a scalar multiple -2/3 of the cubic gradient. The Lean endpoint directly formalizes the source's stated critical equations; it does not attempt an independent differential-geometric development of Lagrange multipliers. MathDB defines the counted points as real solutions of that equation.

## Finiteness of the entire critical set

Finiteness is proved for all nonzero real solutions, not assumed from the finite displayed witness set. Let x be any such solution and a=x_0. If a=0 the equations with coordinate0 force every x_i=0. If a=2 those equations force every x_i=2, contradicting the cubic sum. Hence a is neither0 nor2. Factoring the equation with coordinate0 gives

    (x_i-a)((a-2)x_i-2a)=0.

Thus every coordinate equals either a or 2a/(a-2). Encode x by S={i:x_i=a}, a nonempty subset because0 belongs to it. Write k=|S|≥1. Multiplying the cubic sum by (a-2)^3 and cancelling a^3 gives

    k(a-2)^3 + 8(18-k)=0.

For fixed S this determines a uniquely, because cubing is injective on the reals. It then determines all coordinates. The encoding into the finite powerset of eighteen indices is injective. Consequently the entire critical set C is finite.

## Literal formal endpoint

`Fermat.Critical` contains the nonzero condition, cubic equation and every pairwise equation. Diagonal equations add tautologies to the source's i≠j convention. `Fermat.C` specializes exactly to n17,d3,u all2.

`Fermat.counterexample` proves C.Finite,153≤C.ncard,and ¬C.ncard≤33. `Fermat.claim_false` refutes the universal finite-critical-point bound with odd d≥3,n≥1. The witness satisfies the extra all-nonzero/outside-cone assumptions as proved in `observation_admissible`.

## Scope and significance review points

The source introduces equation (2.1) in its complex ED-degree discussion with generic u; the later real-point question and the MathDB record use finite critical sets. The formal endpoint resolves the literal finite-set MathDB claim. It does not formalize a generic-u perturbation statement. This distinction must be independently reviewed rather than silently identifying finiteness and genericity.

The violation is not an endpoint or wording correction: it uses degree3 and positive, nonzero observation coordinates on a smooth part of the ordinary unscaled cone. Its mechanism is the combinatorial multiplicity of real quadratic branches under coordinate permutations. It is not inferred from a generic upper bound on the total complex ED degree. No minimal dimension, exact total cardinality, or additional discovery count is claimed.
