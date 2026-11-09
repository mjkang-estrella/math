# P3 stop and remaining work

This pilot stops with zero credit. P1 and the normalized quadratic part of P2
compile. P3 is incomplete: there is a genuine exact order-six theorem with an
analytic remainder, but no checked order-two theorem for the other branch and
no simultaneous two-root imaginary-distance comparison. The paired 6/2 claim
is therefore still only partially formalized. P4 was not undertaken. This is
not a refutation certificate, a successful full analytic pilot, or an acceptance.

No absent foundational mathlib theorem has been demonstrated. The inverse
function and analytic-order infrastructure needed here exists. What is missing
is checked application code. In particular:

1. For the slope -3 branch v, extract the actual analytic remainder
   v(x) = -3 + x h(x), h(0) = 3 - 2 i. Direct substitution gives
   F(x,-3) = x (6 - 4 i - 15 x + 9 i x²). The nonvanishing divided
   difference is -2 at 0. This strongly suggests the same method as the
   checked slope -1 proof, but this document is not a Lean proof of it.
2. Deduce `analyticOrderAt (fun x : ℝ => ((x : ℂ) * v x).im) 0 = 2`.
   The first attempts at the order-six analogue failed because `fun_prop`
   did not insert real scalar restriction or transport the complex
   neighborhood to the real line. Explicit `restrictScalars`,
   `Complex.ofRealCLM`, `Complex.imCLM`, and continuity transport solved
   those issues for order six. Thus these are application gaps, not
   evidence that mathlib lacks analytic imaginary-part operations.
3. Obtain a *common* neighborhood and positive constants on which both
   actual roots lie below the real axis, their imaginary distances have
   orders six and two, and their minimum is bounded above and below by
   positive multiples of |x|⁶. Analytic factorization alone is not the
   `HasHalfPlaneContact` predicate.
4. Explicitly transfer normalized u roots to all w roots of the cleared
   denominator, with x = 0 and nonzero x separated. The quadratic theorem
   proves exhaustive normalized roots, not the final zero-set transfer.

The checked order-six mechanism is stronger than a polynomial jet:
F(x,P(x)) = x⁵ H(x) is an exact polynomial identity. For an actual analytic
root u with u(0) = -1, define

g(x) = -H(x) / [A(x)(u(x) + P(x)) + B(x)].

The denominator equals 2 at 0, so g is analytic there; the branch equation
proves u = P + x⁵ g on a neighborhood, and g(0) = 17/4 - i/2. On the
real line P is real, so Im(x u(x)) = x⁶ Im(g(x)). The analytic-order
factorization lemma then gives exact order six. `concrete_order_six`
instantiates this with an actually constructed root; it has no conditional
existence hypothesis.

P4 still needs the explicit graph and shortest-distance certificate; matrix
inverse N/Q identity; reduction over complex bivariate polynomials (not a
Bezout/IsCoprime surrogate); stable bidisk certificate; Cayley zero-set
comparison with uniform constants; exclusion of contact two; and the literal
negation of SourceConjecture. None is supplied as an assumption to a purported
counterexample theorem.

Planning estimate, not a promise: 0.5–2 expert days for items 1–2, another
1–3 days for items 3–4, and 1–3 weeks for P4 including review and replay.
There is no mathematical obstruction found. The measured pilot supports
feasibility but does not meet the requested analytic pair, and is handed back
under the stop rule without acceptance. The review's broader novelty status
is inherited from the root adjudication, not independently re-cleared here.
