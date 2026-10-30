# Complete classical-corollary bridge; NOT a discovery nomination

Credit 0. This is an all-order ordinary proof for the literal arXiv definition,
recorded to explain exclusion as a short classical corollary. It is not an
acceptance claim or a published-version certification.

Fix a nonsingular complex Weierstrass curve y²=4x³-g₂x-g₃ and a closed cycle γ
avoiding infinity. Put p(z)=℘(z), ζ'=−p, ζ(z)=z⁻¹+O(z³), and
2ω=∮γ dz, −2η=∮γ p(z)dz. These are the source's signs and half-periods.
For every integer m≥1, Definition (21) is

    ℬ₂ₘ = (1/2) ∮γ (p^(m−1)(z))² dz.

No positivity restriction on numerical g₂,g₃ or reality restriction on γ is
needed: the assertion concerns coefficients of universal rational polynomials.
Write

    p(t)=t⁻²+Σ_{r≥2} c_r t^(2r−2),
    δ=6g₃ ∂/∂g₂+(g₂²/3) ∂/∂g₃.

The explicit answer, for EVERY m≥2, is

    Â^(m)=(2m−2)! δ c_m,
    B̂^(m)=2m(2m−2)! c_m,
    ℬ₂ₘ=(−1)^(m−1)(Â^(m) ω−B̂^(m) η).                 (A)

At m=1 the literal definition gives Â^(1)=g₂/12, B̂^(1)=0. A zero polynomial
has empty support, as already occurs for the source's power-period positivity.
We do not turn its printed B₂ normalization discrepancy into a counterexample.

## 1. Classical input and an independent verification

Buchstaber–Bunkova, arXiv:1204.3784v1, §8.4 p15 Theorem37 (explicitly called
Weierstrass's theorem) states

    δσ = (1/2)σ''+(g₂t²/24)σ.

The exact operator and invariant normalization were read in the PDF and visually
checked. Apply −∂t² to its logarithmic form, using (logσ)'=ζ:

    δp = 2p²+ζp'−g₂/3.                               (B)

Indeed δlogσ=(−p+ζ²)/2+g₂t²/24, whose negative second derivative is
p''/2−p²+ζp'−g₂/12=2p²+ζp'−g₂/3.

There is also an independent elementary verification, without assuming the heat
identity. Let W=2p²+ζp'−g₂/3. From p'²=4p³−g₂p−g₃ and
p''=6p²−g₂/2 one computes

    W'=3pp'+ζp'',    W''−12pW=−3g₃.

Differentiating the equation for p by δ shows that δp satisfies the same
inhomogeneous equation, since δg₂=6g₃. Both series have no negative or
constant terms and have coefficients 3g₃/10 at t² and g₂²/84 at t⁴.
For W these follow by substitution of
c₂=g₂/20,c₃=g₃/28,c₄=g₂²/1200; for δp they follow by differentiating c₂,c₃.
Their difference H is an even series starting at t⁶ and satisfies H''=12pH.
If its first nonzero term is at exponent j≥6, comparison of exponent j−2 gives
(j(j−1)−12)H_j=0, impossible. Thus H=0 as a Laurent series. Convergence
near zero gives the analytic identity there. Equivalently this is a formal
coefficient proof over Q[g₂,g₃]. This verifies the classical normalization in (B).

## 2. Literal period bridge, including both period coefficients

For t nonzero and sufficiently small so ±t are distinct modulo the lattice,
comparison of poles and constant terms in z gives

 p(z)p(z+t) = p(t)(p(z)+p(z+t))
             +p'(t)(ζ(z)−ζ(z+t))
             +2p(t)²−g₂/4+p'(t)ζ(t).                 (C)

Here is a full check. At z=0 the left side has principal part
p(t)/z²+p'(t)/z; at z=−t it has p(t)/(z+t)²−p'(t)/(z+t).
The first two terms on the right have exactly those principal parts. Their
subtraction leaves an entire elliptic function, hence a constant. The constant
term of the left side at z=0 is p''(t)/2; that of the first two terms is
p(t)²−p'(t)ζ(t). Subtract and use p''=6p²−g₂/2 to obtain (C).
Although ζ is quasiperiodic, its difference in (C) is elliptic.

Take t in a small disk such that the compact contour and its small translations
avoid poles. The translated p-period is constant: its t derivative is the
period of the exact differential p'(z+t)dz, which vanishes. Therefore
∮p(z+t)dz=−2η. If
J(t)=∮(ζ(z)−ζ(z+t))dz, then J(0)=0 and J'(t)=∮p(z+t)dz=−2η;
thus J(t)=−2ηt. These statements work on a lifted cycle, and the differences
are single valued on the torus. Integrating (C) gives the locally analytic identity

 (1/2)∮p(z)p(z+t)dz
   = ω(2p(t)²−g₂/4+p'(t)ζ(t))−η(2p(t)+tp'(t))
   = ω(δp(t)+g₂/12)−η(2p(t)+tp'(t)).                (D)

The cancellations on the right remove its apparent singularity at t=0.
Taylor expansion under the compact contour integral is valid uniformly for
small t. Its coefficient of t^(2m−2) is

    [1/(2(2m−2)!)] ∮p(z)p^(2m−2)(z)dz
      = (−1)^(m−1) ℬ₂ₘ/(2m−2)!,

by m−1 integrations by parts. Boundary terms vanish because p and all of its
derivatives are periodic. This is precisely equation(23) and Proposition7
in the source, rather than a definition of a substitute recurrence.
For m≥2 the same coefficient on the right of (D) is
ω δc_m−η(2m)c_m. The constant coefficient is g₂ω/12.
This proves (A) for every m. In particular both signs and the factor 1/2 are fixed.
Arbitrary closed cycles follow by additivity; small loops around infinity give
zero for these zero-residue differentials. The two basic cycles also give
uniqueness of the coefficients by their nonzero Legendre determinant. Hence
these are the source's universal polynomials, not merely values for one period.

## 3. Coefficient positivity at every order

The Laurent recurrence, already printed in Grosset–Veselov pp13–14, is

 c₂=g₂/20, c₃=g₃/28,
 c_r=3/((2r+1)(r−3)) Σ_{s=2}^{r−2} c_s c_(r−s)  (r≥4).

Its prefactor is positive. Induction gives nonnegative rational coefficients
and weighted support 2a+3b=r for c_r. Every monomial of that weight actually
occurs positively: a+b=1 is a base case; if a+b≥2, remove a g₂ when a>0
(otherwise remove a g₃), leaving weight at least2, and use the corresponding
summand c₂ c_(r−2) or c₃ c_(r−3). Induction completes this assertion.

The operator δ sends each nonconstant positive monomial to a nonzero sum of
positive monomials. Thus c_m and δc_m have positive coefficients on their
supports for every m≥2. More strongly δc_m contains every allowed monomial
of weight m+1: for target g₂^a g₃^b, if b≥1 use the g₂ derivative of
 g₂^(a+1)g₃^(b−1); if b=0 then a≥2 and use the g₃ derivative of
 g₂^(a−2)g₃. The preimages have weight m and occur positively in c_m.
All factorial multipliers in (A) are positive. This proves the FULL Conjecture2
coefficient claim for the literal definition, with no finite-order restriction.

## Scope, strongest objection, and feasibility

This does NOT prove Conjecture1 about all λ coefficients. Proposition4 alone
was insufficient; (C)–(D) and the classical invariant derivative supply the
missing bridge. A reversal of the ζ sign, use of full rather than half periods,
or omission of the 1/2 would falsify the identity; the exact checker independently
reduces the literal squares and the IBP expression through m=20 and compares
both with (A). That finite check diagnoses conventions, and is not the proof.
The direct ODE verification above additionally avoids reliance on an unchecked
heat-equation convention.

This is a short consequence of a published classical identity and the positive
Laurent recurrence already in the primary paper. No claim of a previously
unpublished theorem is made. No direct earlier paper explicitly announcing
Conjecture2 as solved was located in the bounded search. Campaign excludes
routine corollaries regardless. The 2006 VoR body was not obtained (403), so
its exact revisions remain a source-comparison HOLD.

Lean: an honest literal endpoint would quantify nonsingular complex invariants,
cycles, contour integrals and the Weierstrass objects, then identify their two
polynomial coefficients with (A). Formalizing only δ preserving polynomial
positivity would leave the essential analytic bridge unproved. No complete
ready-to-replay Lean endpoint is claimed. No Lean or helper Lean was written;
classical exclusion and source hold make large formal investment inappropriate.
Root alone owns independent review and acceptance.
