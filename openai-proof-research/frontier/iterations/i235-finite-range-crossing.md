# I235 — finite-range quantitative crossing continuation

**Verdict: unresolved; no tenth finding.** The quantitative forward-crossing estimate and finite mean marked regeneration duration remain unproved for the full finite-range class, including its d>=4 finite-support subclass. No exact-scope counterexample was found. All pinned OpenAI results and lower operations at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` were stipulated true within their hypotheses. I232 A232/B232 remain technical inputs.

The base class is a stationary ergodic law Q of full nearest-neighbor transition rows on Z^d, d>=3, with a common positive ellipticity lower bound and independence of row sigma-fields on all deterministic sets at infinity-distance greater than a fixed finite r, including infinite sets. Assume almost-sure escape in a fixed nonzero real direction. The I232 spatial-radius result gives a deterministic ray and a signed-coordinate reduction; its small inverse moment supplies some alpha>0 with E_Q q(0)^(-alpha)<infinity.

The completed [analytic notes](../experiments/i235_finite_range_crossing/analytic-attempt.md) establish four technical steps, without claiming a new ballisticity case:

1. A finite-range buffered tilted-record argument gives exponentially small probability of leaving a transverse box of width C N^2 before exiting a height-N strip.
2. The existing small inverse moment yields an unconditional positive fractional moment of the actual marked duration: with A=2d+(2d+1)/alpha, E tau^s<infinity for every 0<s<1/A. This does not give E tau.
3. The marked-renewal conversion is now complete. If the unpaid estimate Q(a_N<N^-beta)<=N^-D eventually for every D>0 holds for some beta<1, it implies all finite moments of marked width and duration. The exact generating function is

       sum P(L>n)t^n = [1-t+xi t^M(1-sum (u_n-u_(n+1))t^(n+1))]^-1.

   Its denominator tends to xi p>0. Differentiation from below at t=1, followed by monotone convergence of nonnegative coefficients, handles the initial gap and shift. No false nonnegative defective-convolution identity for the marked masses is used.
4. In d>=4, the independent common-word transverse endpoint difference has a heat-kernel bound C(n+1)^(-(d-1)/2), hence is transient, without a second moment. An explicit independent decorated-renewal example has the same stated radius/endpoint inputs and infinitely many trace contacts. It is not asserted to be an RWRE law. Thus endpoint transience alone does not establish the required path comparison.

The finite-alphabet route also remains incomplete. The actual range-one three-row mediator field has forbidden neighboring patterns. Its entropy relative to the all-row product is infinite; an independent seam splice even has infinite entropy relative to Q on a two-row window. A valid deterministic finite-collar mutual-information bound costs at most the number of collar rows times log(alphabet size), but that cost is not controlled at the iid proof's logarithmic episode scale. No conditional independence after revealing a collar is assumed.

The precise unpaid work is (i) a same-direction shared-Q multiwalk estimate controlling proximity of active rows throughout decorated words, sufficient for the adaptive clipping/rapid-loss/separated-stage construction, and (ii) a stopped-window entropy law relative to the actual Q upper field with the required episode cost. The complete iid source argument was read, including its diagonal occupation and stationary contradiction proofs. Its first-hit restart and independent-tail splice identities are the identified failures of direct transfer. A direct integrable-duration proof remains an alternative; the fractional-moment calculation supplies no exponent bootstrap.

[Source contracts and primary-literature limits](../sources/i235_finite_range_crossing/literature.md), [attempts and failures](../experiments/i235_finite_range_crossing/reading-and-failures.md), and [input authentication](../experiments/i235_finite_range_crossing/input-authentication.json) provide the scoped record. Only assigned I235 paths were written. No subordinate agents, live I231/I234 outputs, research code, tests, numerical experiments, parameter scans, snapshots, seals, shared edits, staging, commits, or publication were used. Detached hashes accompany delivery. Nine accepted findings remain nine.
