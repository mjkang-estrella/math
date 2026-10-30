# Complete proof outline and exact certificate

Use precisely the C recurrence and rho/sigma sums in paper.pdf Section1, Yuster Lemma3.5 and Corollary3.7. The Lean definitions sourceC, sourceRho, sourceSigma and sourceP literally implement those formulas. Integral dynamic rows realize (k−1)! C; their recurrence and initial/zero entries are proved, including the signed integer multiplier.

For canonical ψ in [0,1] with (1−ψ)^48=ψ, put φ=1−ψ and α=φ^47. Since φ+φ^48=1, φ(1+α)=1 and α(1+α)^47=1. This function of α is strictly increasing on nonnegative reals. Exact rational arithmetic establishes a(1+a)^47<1<b(1+b)^47 for a=61/1000,b=613/10000. Thus a<α<b; the parameter is constructed from the source equation and is not supplied as a hypothesis.

At x=1/100,1/10,1/2,3/5,4/5 the exact rho evaluations are all negative. The endpoint checks are a rho−sigma<0 at the first/third/fifth points, and b rho−sigma>0 at the second/fourth. Because increasing α decreases α rho−sigma, these imply alternating signs −,+,−,+,− for the actual p48. Every endpoint rational inequality is kernel-checked in YusterArithmetic; real transfer is proved in YusterSigns.

The intermediate value theorem produces a root in each adjacent open interval; their strict separation proves distinctness and places all four in (0,1). Nonzeroness follows from the first strict sampled sign. The four-element set injects into the filtered root multiset's finite support, whose cardinality is no larger than its multiset cardinality. Therefore the multiplicity count is at least four, contradicting at most two. FourRoots and YusterRootCounterexample certify every step, culminating in source_rootcount_ge_four and source_conjecture_357503_false.

The standard-library independent exact checker uses a closed finite-difference expression for C rather than the formal recurrence; it also verifies small source-table normalizations. Its computations are cross-checks, not additional axioms. The full proof, including rational inequalities, is Lean-certified.
