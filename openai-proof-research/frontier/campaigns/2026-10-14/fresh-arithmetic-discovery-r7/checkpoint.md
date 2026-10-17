# R7 checkpoint: Serre-positivity screen

Myeongjin Kang; no affiliation. 2026-10-16. Original prose CC BY 4.0. Third-party inputs remain private.

**PRE_FREEZE_SCREEN_UNPAID. No candidate frozen; counted=false.** This is a bounded operation-level screen, not a completed discovery or positive eligibility clearance. The campaign remains 6/10 by the parent assignment. Earlier CS/RF/r5/r6 artifacts were not edited.

## Actual source contract and paid operations

At stipulated revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, family 193's `Positivity-of-Serres-Intersection-Multiplicity-September-23-2026/build/sections/introduction.tex`, `thm:main`, proves strict positivity for every regular Noetherian local ring and nonzero finite modules whose tensor product has finite length and whose dimensions sum to the ambient dimension. The complete introduction was read. Its `cor:tangent-cone` already gives the product-of-multiplicities lower bound, with the exact tangent-cone equality criterion, when the graded tensor product has dimension at most one. It also explicitly applies Kurano–Roberts to one ordinary and one symbolic power in ramified mixed characteristic. Neither is an unpaid proposal.

Actual primary comparison: Kurano–Roberts, *The Positivity of Intersection Multiplicities and Symbolic Powers of Prime Ideals*, Section 3 through the proof of Theorem 3.2, constructs a nonzero initial-form element in the forbidden kernel using a regular alteration with Cartier exceptional fiber. Thus applying stipulated positivity to their theorem is already paid. Skalit, *Intersection Multiplicity of Serre in the Unramified Case*, Section 3.2 (Theorem 3.4 through Proposition 3.10 and their proofs) uses Fulton's blowup identity and reduces its correction to local positive multiplicities precisely when the intersection has finite support. The same source's Theorem 3.11 credits the equicharacteristic geometric result to Fulton–Lazarsfeld. Changing the available positivity input does not create a new blowup operation.

## Exact obstruction beyond finite support

Let A be regular local of dimension d, let P,Q be prime with A/(P+Q) of finite length and dim(A/P)+dim(A/Q)=d, and denote the blowups at the closed point by X',Y',Z'. Put S=Y' intersect Z'. The actual blowup identity reads

    Delta = chi^A(A/P,A/Q) - e(A/P)e(A/Q)
          = sum_(i,j) (-1)^(i+j) length_A H^i(X', Tor_j(O_Y',O_Z')).

The finite-support argument does not extend merely by applying strict local positivity to more points. Suppose C is an irreducible component of S of positive dimension r, and eta is its generic point. The finite-type catenary dimension formula gives

    dim O_X',eta = d-r,
    dim O_Y',eta = dim(A/P)-r,
    dim O_Z',eta = dim(A/Q)-r.

The tensor product of the last two local modules has finite length: eta is a minimal point of the intersection support. But the sum of their dimensions is d-2r, strictly smaller than d-r. Consequently Serre vanishing gives their local Tor Euler characteristic ZERO. Strict positivity is inapplicable at eta. Conversely, at a closed point of a positive-dimensional component the tensor product has positive-dimensional support and is not of finite length. It is again outside the source theorem. This is a failure of the needed hypotheses, not a counterexample to stipulated positivity.

The curve-support case makes the missing invariant especially visible. Suppose the set-theoretic support S is one-dimensional and choose an ample line bundle L on it (the exceptional polarization suffices). For each Tor sheaf F_j, the coefficient of n in chi(F_j tensor L^n) is the sum over curve components C of length_(O_X',eta_C)(F_j,eta_C) times deg_L(C), by dévissage/Hilbert polynomials. The alternating sum of these generic lengths is zero by the preceding local vanishing. Thus the alternating Hilbert polynomial is CONSTANT. Local positivity supplies no sign for that constant Delta. Even in the simplifying situation of sheaves on a smooth reduced curve, a virtual rank-zero class can have either sign of Euler characteristic: on P^1, [O]-[O(1)] has Euler characteristic -1, and its negative has +1. These are logical countermodels to rank cancellation implying nonnegativity, not claimed realizations as strict-transform Tor classes.

In the additional clean lci curve-intersection situation with a rank-one excess bundle E, the Koszul excess description is F_0=O_C and F_1=E dual, hence Delta=deg(E). Establishing positivity of this particular excess degree would be a global geometric operation. That auxiliary description is only an illustration of what remains to be controlled; no clean/lci hypothesis is inserted into a proposed full theorem and no such subclass is offered for counting.

The exact unpaid operation is therefore a proof that the global derived-intersection Euler degree is nonnegative, and strictly positive whenever S is nonempty, for arbitrary positive-dimensional exceptional intersections in ramified mixed characteristic. No such proof was obtained. The full general product lower bound/equality criterion is already Skalit's Conjecture I, not a newly formulated target. Removing its geometric restriction without a new degree-control mechanism would violate this campaign's discovery criterion. Accordingly this round does not freeze that conjecture, claim a full proof, or replace it by finite support, clean curves, numerics, or a conditional bridge.

## History boundary

Old I28 develops small Cohen–Macaulay and Kurosh/involution targets; I204 develops Egyptian fractions, potential integral character varieties, and Gaussian moat; I145 develops specified class-group cosets. Those routes were excluded. The Gaussian propeller screen also encounters R012/I38 and was not pursued. Earlier r5/r6 exclusions and the parent's exclusions of 200/204/208, 259 and 271 persist. A focused phrase search of the iteration and current campaign Markdown bodies returned no family-193 development hit, but a negative text search is not a full semantic history audit or eligibility clearance. Because no new mechanism was obtained, no final history clearance was attempted.

## Decision

Preserve this as a paid-route rejection and a precise local-to-global obstruction. It supplies no new accepted result and no independent PASS. Further work would need an actual ramified excess-degree mechanism, not another application of local strict positivity or an additional coefficient/dimension transfer.
