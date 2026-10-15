# I345 contribution screen and submission scope

2026-10-14. Parent research note; **not an independent contribution PASS**.
I345 remains a candidate and earns no acceptance increment.

## Exact proposed advance

I345 claims dimension-only interior C^{1,alpha_n} estimates for every bounded
weak p-harmonic function, simultaneously for all finite p >= 3. No original
gradient lower bound, sign restriction, or convexity of level sets is assumed.
The complete proof is the pre-existing
`frontier/experiments/i345_lifted_p_gradient_research/analysis.md`.
The OpenAI infinity-harmonic estimate and its exact source interfaces remain
stipulated at revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

## Primary-literature comparisons

1. Peng–Zhang–Zhou, [arXiv:2310.08093v3](https://arxiv.org/html/2310.08093v3),
   introduction and Theorem 1.1: the actual class is potentials in convex
   rings, with prescribed constant data on the two boundary components.
   Its theorem provides local C^1 convergence of p-potentials and nonvanishing
   limit gradient. This establishes a substantial antecedent, but does not
   state the unrestricted, quantitative, dimension-only estimate in I345.
   Its introduction explicitly distinguishes unrestricted p-uniform gradient
   regularity from ordinary fixed-p estimates. The published version is
   [PLMS 130 (2025), e70062](https://doi.org/10.1112/plms.70062); only its
   abstract was additionally checked. No claim that its unseen final text
   has no further relevant theorem is made.
2. Bungert, [arXiv:2302.08462v2](https://arxiv.org/html/2302.08462v2), Theorem 1
   and Remarks 2.4–2.5: provides value convergence rates with explicit
   global Hölder and boundary-data hypotheses. It does not give unrestricted
   gradient convergence. Combining an accepted I345 with its value estimate
   through the standard finite-difference inequality would give an interior
   gradient rate. That combination would be a credited corollary, not an
   additional acceptance.
3. Lee–Lee, [arXiv:2609.09966v1](https://arxiv.org/html/2609.09966v1), Theorems
   1.2, 1.3 and A: the sharp inhomogeneous regularity result is restricted
   to p sufficiently close to 2. Theorem A records the older
   Araújo–Teixeira–Urbano reduction: a quantitative homogeneous exponent
   strictly above 1/(p-1) yields the sharp bounded-forcing exponent.
   Its scope differs from I345's large-p uniform estimate.

The narrow searches used combinations of “p-harmonic”, “uniform”,
“C1 alpha”, “gradient”, and “infinity”, and separately sought value-rate and
convex-ring antecedents. They do not establish worldwide priority. An
attempt to read the 2018 IMRN article directly through the publisher failed;
its actual theorem has not been silently treated as read. Theorem A above is
the inspected primary-paper interface for any proposed transfer.

## Conditional application to a precise MathDB problem

[MathDB 405360](https://mathdb.com/p/405360/the-c-p-regularity-conjecture)
asks for the sharp C^{1,1/(p-1)} conclusion for **inhomogeneous** equations
with bounded right-hand side for every p>2 in every dimension. The page was
read on 2026-10-14. No significance ranking was shown; none is assigned.

If I345 is accepted, choose its alpha_n and any

    P_n > max(3, 1 + 1/alpha_n).

For each fixed p >= P_n the strict exponent inequality pays Theorem A's
homogeneous premise. Consequently bounded-forcing solutions have the sharp
local C^{1,1/(p-1)} regularity in that large-p range. The inhomogeneous
constant may depend on p; I345 does not remove that dependence.

This implication is a **conditional, standard transfer**, contingent on the
candidate and the cited theorem interface. It is useful for the same paper
but supplies no second result count. It leaves an intermediate-p interval
uncovered even when combined with near-2 literature. Neither I345 nor this
note solves the full MathDB 405360 conjecture.

## Contribution question still requiring independent judgment

After assuming all pinned inputs, can an older standard stability theorem
already give the unrestricted p-uniform C^{1,alpha} estimate? A contribution
review must try to construct that reduction. Merely taking a value limit
to an infinity-harmonic function gives no quantitative common gradient
Hölder bound. The proposed additional work is the critical-safe constrained
lift, finite-positive-viscosity rigidity, the uniform small-solution family,
and the repaired unequal-parameter slope comparison. Their validity is
under separate proof review; their novelty is not certified here.
