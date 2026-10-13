# I232 — finite-range ballisticity continuation

**Verdict: target unresolved; no tenth finding.** This resumed I227 after its administrative interruption, retained family 220, and did not read live I230/I231 work. All pinned OpenAI results and lower operations at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` were treated as true. No upstream audit was attempted.

The exact target is: for a stationary ergodic law Q of nearest-neighbor transition rows on Z^d, uniformly bounded below by kappa>0 and independent on every two deterministic row sets at infinity-distance greater than a fixed finite r (including infinite sets), does P_0(X_n.ell -> +infinity)=1 imply X_n/n -> v with deterministic v.ell>0? The desired range is d>=2; the stipulated finite-range zero-one input is d>=3 and would there upgrade positive escape probability to probability one.

The actual finite-range source already proves exact iid marked regeneration words and finite mean width. Those are prior work. The iid ballisticity source additionally proves a superpolynomial lower-tail estimate for quenched forward crossing probability and converts it into finite mean duration. Those extra operations are not supplied for correlated rows by the zero-one theorem.

Two routes were pursued with analytic proofs of intermediate claims:

- **A232, d>=3:** for the source's marked words in any fixed normalized direction with positive nonbacktracking probability, their full spatial radius has finite mean, without the two-sign coexistence hypothesis in the finite-range source's radius proposition. A fixed constant-weight connector separates a forward template from the old active rows by tilted and height barriers. This adapts the iid source's argument; it gives a limiting ray, not positive speed.
- **B232, d>=2:** in a coordinate direction with positive nonbacktracking probability, q(0)=P_(0,omega)(never below 0) is positive a.s. and E_Q q(0)^(-alpha)<infinity for some alpha>0. A buffer m>r before the conditional survival test repairs the precise use of upper-row independence. It does not establish an exponent above one or finite mean regeneration duration.

Both are technical transport lemmas, not nominated substantive findings. Their complete hypotheses, proofs, and source labels are in [analytic-attempt.md](../experiments/i232_finite_range_ballisticity/analytic-attempt.md). The existing iid CLT/LLN and velocity-hemisphere consequences were excluded from nomination.

The counterexample search found no verified exact-scope example. A fully specified stationary uniformly elliptic 1-dependent field does show that even conditioning on one observed step can make two unconditionally independent separated rows dependent. It refutes the proposed conditioning shortcut, without asserting transience. An independently derived classical 1D transient zero-speed law lifts to higher-dimensional layers but violates finite dependence; a fixed-width local tube has uniformly bounded mean exit time regardless of length. The BZZ primary counterexample is polynomially mixing and opposite-ballistic, not an eligible finite-dependent trap. No exhaustive nonexistence claim is made.

**Precise unpaid work:** prove a finite-range counterpart of the iid same-direction multiwalk crossing estimates, keeping each adaptive test's active rows separated from fresh rows, controlling projected-diagonal occupation and cumulative mass cost, and supplying a valid stationary reference-field entropy law across collars. One explicit sufficient quantitative target is: after the limiting-ray coordinate reduction, there exists beta in (0,1) such that for every D>0,

    Q(P_(0,omega)(T_N<T_-1) < N^(-beta)) <= N^(-D)

for all sufficiently large N. This is an unpaid estimate, not an extra assumption asserted as a theorem. Its conversion to duration integrability must also respect the source's MARKED renewal masses `bar u_H=xi u_(H-M)` and the initial gap. A verbatim iid proof is not justified. Directly proving finite mean duration is an alternative unsolved terminal step.

[Source contracts and literature](../sources/i232_finite_range_ballisticity/literature.md) distinguish read statements from unread proofs. [Reading and failures](../experiments/i232_finite_range_ballisticity/reading-and-failures.md) record unsuccessful routes, retrieval errors, and the limited reading scope. [Input authentication](../experiments/i232_finite_range_ballisticity/input-authentication.json) gives retained source ranges and provenance hashes; detached output hashes accompany delivery. No snapshots or seals were made.

Only the assigned I232 paths were written. No subagents, research code, tests, scans, numerical experiments, shared edits, staging, commits, or publication occurred. Parent-owned independent proof and contribution gates remain unrun. Nine accepted findings remain nine.
