# I293 — independent contribution review of I289

2026-10-13. **Contribution: TECHNICAL. Analytic assessment: no flaw found in the frozen target. Literature priority: UNRESOLVED. No acceptance claim.** The user's metadata update makes the current ledger 13/20; I289's historical twelve-count statements remain frozen. This review implies no further count change.

## Frozen scope and independence

Read the complete I289 analysis, report, reading log, literature note and authentication. Analysis SHA256: 063466c7963eb9696af1d6fe4e07a3bbb328842a55b4ecfa09b6759004be9e02. Report SHA256: 4e68aa6bcfd55732a9dc2f08240e56928beacae44fd6deb7a4a744a6f4eb9fbe. Both match the assignment. The authorized parent swap-test supplement was read as shared mathematical input, never as independent proof validation. Neither the author nor the parent supplies an independent gate for this review. R019 was not read.

All OpenAI results at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are true by stipulation. Actual family-276 paper, output, thermal, partners and special sources were read completely, freshly fetched at their immutable URLs, and checked against retained bytes and exact-path Git blobs. Their truth was not audited.

The target fixes 0<s<=1/3 and A_s with Bloch multipliers (s,s,s²). For every n>=1 and every normalized pure n-qubit state, in nats and unhalved trace norm,

    d_eq(psi)² := inf_(equatorial pure product phi) ||Ppsi-Pphi||_1²
      <= [240+32/(1-s²)] D_s(psi)/s² <=276 D_s(psi)/s²,
    D_s(psi)=S(A_s^tensor n(Ppsi))-n h((1+s)/2).

There is no phase-rank, support, complexity, Schmidt-rank or near-minimizer hypothesis. The same unsimplified coefficient works to s=sqrt(2)-1; this is the same result, not a second nomination. Neither non-EB GAD nor uniformity at s=0 is asserted.

## Decisive adverse reduction from actual older results

The classification does not rest on keyword overlap, proof length, or Bae's depolarizing theorem. Here is an explicit reduction retaining every n and every pure input. It does not take the author/parent drift estimate as a premise.

The old inputs are Shor's Theorem 1 proof, especially (5) and (7)–(14); Harrow–Montanaro Lemma 2 with its Appendix B proof, including mixed states; and Soleimanifar–Wright Theorem 15 with its complete §2.1 induction. I280's already paid amplitude estimate is the remaining project input. All intervening estimates below are derived.

### 1. The old purity formula already gives arbitrary-ensemble drift

For a state tau on m parties define

    Q_m(tau)=2^(-m) sum_(S subset [m]) Tr(tau_S²).

Harrow–Montanaro Lemma 2 says this is the two-copy product-test acceptance probability, even for mixed tau. Write T_m(chi)=Q_m(Pchi) and F_m=1-T_m for pure chi, with T_0=1. For pure psi on a first party A and tail B, let rho=Tr_A Ppsi and rho_A=Tr_B Ppsi. The equality of complementary marginal purities gives

    T_n(psi)=Q_(n-1)(rho).                                      (1)

Indeed subsets of all n parties pair as S subset B and its full complement; both have the purity of rho_S. Equivalently, this follows by expanding the swap projectors. No productness or tail-rank restriction occurs.

Take any finite pure-state ensemble rho=sum_i p_i sigma_i, sigma_i=Pchi_i. Expanding the squares in the old formula gives the exact variance identity

    sum_i p_i T_(n-1)(chi_i)-T_n(psi)
      =2^(-(n-1)) sum_(S subset B) [sum_i p_i Tr(sigma_(i,S)²)
                                               -Tr(rho_S²)]
      =(1/2) sum_(i,j) p_i p_j 2^(-(n-1))
                                  sum_(S subset B) ||sigma_(i,S)-sigma_(j,S)||_2².
                                                                    (2)

For any traceless Hermitian Y, splitting its positive and negative eigenvalues proves ||Y||_2²<=||Y||_1²/2: each part has eigenvalue sum ||Y||_1/2, and its squared sum bounds its sum of squares. Partial trace contracts trace norm on Hermitian differences. One elementary proof uses trace-norm duality and ||K tensor I||_infinity=||K||_infinity. For the pure projectors sigma_i,sigma_j this yields

    ||sigma_(i,S)-sigma_(j,S)||_2²
      <=(1/2)||sigma_(i,S)-sigma_(j,S)||_1²
      <=(1/2)||sigma_i-sigma_j||_1²
      =2(1-Tr(sigma_i sigma_j)).

The subset average in (2) has total weight one. Consequently

    0<=sum_i p_i T_(n-1)(chi_i)-T_n(psi)
          <=1-Tr(rho²)=1-Tr(rho_A²),
    F_n(psi)<=sum_i p_i F_(n-1)(chi_i)+1-Tr(rho_A²).       (3)

This is an elementary corollary of the old mixed-state purity formula and norm contractivity, with a coefficient smaller than I289's 2(1-Tr rho_A²). The nonnegativity here follows from squared Hilbert–Schmidt variances; the target's weaker argument need not assert a sign. Empty subsets, repeated ensemble vectors and zero weights cause no difficulty. There is no sum of original single-site impurities and no mixed-input soundness assertion.

### 2. Shor's existing entropy recursion pays (3) without any tensorization assumption

Suppose a finite-dimensional channel Phi has a finite rank-one measure-and-prepare representation and minimum output entropy mu, and suppose

    S(Phi(tau))-mu >=c(1-Tr(tau²)) for every input state tau, c>0.   (4)

Rank-one effects on the first site of a pure input produce pure conditional tail inputs, with probabilities p_i and average rho. The same classical extension used in Shor's proof gives

    D_n(psi)>=c(1-Tr(rho_A²))+sum_i p_i D_(n-1)(chi_i),             (5)
    D_n=S(Phi^tensor n(Ppsi))-n mu.

Mixed preparation states are permitted: their entropies and the Shannon terms cancel between the two classical-block entropies in SSA. This is a direct specialization of Shor's proof, not an attribution of stability to the statement of his additivity theorem.

An induction simultaneously applying (3) and (5) gives

    c F_n(psi)<=D_n(psi).                                         (6)

For n=1, F_1=0 and D_1>=0. At the induction step replace c F_tail by D_tail in (3) and use (5). This is also the exact same-tree telescoping. No branch selection, exponentially rare event, growing coefficient, or desired entropy stability tensorization is assumed.

For the target channel,

    A_s=s E_X+s E_Y+s² E_Z+(1-2s-s²) R.

The coefficients are nonnegative for 0<s<=sqrt(2)-1. Dephasing effects are weighted rank-one Pauli projectors; use weighted Z projectors and preparation I/2 for R. Effects sum to I, so the conditional tail ensemble in (5) is precisely authorized by Shor's representation. Zero coefficients at the endpoint are omitted.

For a qubit tau with Bloch vector r, let

    u=s²(r_x²+r_y²)+s^4 r_z²,
    G(u)=h((1+sqrt(u))/2), mu=G(s²).

Since -G'(u)=atanh(sqrt(u))/(2 sqrt(u))>=1/2, including its limit at zero,

    S(A_s(tau))-mu
      >=(s²-u)/2
      >=s²(1-|r|²)/2=s²(1-Tr(tau²)).

Thus c=s², and (6) yields F_n<=D_s/s² for every n and pure psi. This stronger auxiliary bound demonstrates the reduction; it is not a separately nominated theorem.

### 3. The actual older global soundness closes arbitrary productness

Let omega=max_(pure product Phi)|<Phi,psi>|² and epsilon=1-omega. Soleimanifar–Wright Theorem 15 states

    T_n(psi)<=2/3+omega²/3.

The source's overlap is squared overlap. Its induction was checked: the symmetrized off-diagonal Schmidt terms are normalized, their first-site states are orthogonal, retaining only the largest diagonal term gives the displayed bound, the two subtraction sums in (3) are nonnegative, and lambda_1 times the tail product overlap is at most omega. This works for all local dimensions and all n, without a local Taylor radius. Hence

    epsilon<=3F_n<=3D_s/s².                                     (7)

Harrow–Montanaro already supplies global dimension-independent soundness with worse constants. Soleimanifar–Wright supplies the convenient exact coefficient. Product-test soundness itself is spent literature, not the I289 contribution.

### 4. Paid amplitude control and ordinary Hellinger rounding close the actual minimizer family

Shor and global soundness alone give arbitrary products, not equatorial products. The pinned GAD recursion and I280 already give

    D_s>=c_s KL(q||u_n), c_s=(1-s²)s²/2,
    q(x)=|psi(x)|², u_n(x)=2^(-n).                               (8)

To check that dependency, retain every computational conditional population in family-276 eq:recursion. The determinant formula is gamma/4+gamma(1-gamma)(p-1/2)² with gamma=1-s². The derivative g'>=2 and KL(Bern(p)||Bern(1/2))<=4(p-1/2)², followed by the chain rule, give (8). This uses full laws, not merely one-site marginals. Zeros of q are allowed.

Choose a closest product Phi and let p(x)=|Phi(x)|². Round its factors to equal amplitudes with their relative phases preserved, producing the equatorial product Phi_hat. Set H²(a,b)=sum_x(sqrt(a(x))-sqrt(b(x)))². A global phase aligns Phi with psi, and the reverse triangle inequality for each amplitude gives

    H²(p,q)<=2(1-sqrt(1-epsilon))<=2epsilon,
    H²(q,u_n)<=KL(q||u_n)<=D_s/c_s.

The second line follows from Jensen's affinity bound a>=exp(-KL/2) and 2(1-a)<=KL. The squared Euclidean triangle inequality gives H²(p,u_n)<=4epsilon+2D_s/c_s. Product phases align the overlap <Phi,Phi_hat> with the affinity sum_x sqrt(p(x)u_n(x)), including pole factors. Pure-projector trace distance and its squared triangle inequality therefore give

    d_eq(psi)²<=40epsilon+16D_s/c_s
              <=[120+32/(1-s²)]D_s/s²
              <=[240+32/(1-s²)]D_s/s²<=276D_s/s².                (9)

The smaller coefficient in the middle is only a containment certificate for the requested theorem, not a new nomination or acceptance. Every step has constants independent of n and no restriction on psi. Thus this adverse reduction recovers even the stated numerical constant, not just a weaker fixed-complexity analogue.

## Independent analytic check of the frozen assembly

The author's weaker pairwise drift is also valid. H is a contraction; the quadratic expansion cancels linear terms; the pure-projector trace norm squared is 4(1-overlap); averaging gives 2(1-Tr rho²)=4 det rho_A. Purity is essential for the swap identity (4.1). The entropy gap 2s² det rho_A equals s²(1-Tr rho_A²), so its same-tree comparison gives the target's F<=2D_s/s², then epsilon<=6D_s/s² and the coefficient 240. The rounding in the frozen §7 agrees with the independently derived calculation above.

I found no reversed SSA direction, missing spectator factor, original-marginal summation, optimizer-alignment premise, hidden rank assumption, or entropy-continuity transport. Pure conditional tails follow from rank-one measurement effects even when preparations are mixed. Nonnegative terminal deficits may be discarded. At D_s=0 the soundness and full-law KL bounds force an equatorial product. One-site inputs, zero probabilities, empty tails, pole factors, deterministic conditional bits and the endpoint s=1/3 are covered. The unsimplified interval extension ends when the explicit convex representation loses positivity; it does not reach non-EB parameters. This analytic contribution review is not an administrative acceptance or a claim that a separate formal proof gate has been passed.

## Concrete comparison and contribution judgment

**Shor:** the actual proof already preserves the marginal output entropy and all partner branch entropies. I289 retains its one-copy impurity budget instead of immediately minimizing it. The rank-one refinement and Bloch calculation are elementary specializations. The old theorem alone does not literally state I289.

**Harrow–Montanaro:** Lemma 2 already evaluates the mixed-state quadratic test as an average of marginal purities. Equations (1)–(3) above obtain the needed arbitrary-ensemble drift by quadratic variance and ordinary trace-norm contractivity. Their Theorem 1 already addresses arbitrary tensor length and arbitrary local dimension. This is the concrete old-result reduction, not a claim that testing productness automatically pays GAD entropy.

**Soleimanifar–Wright:** Theorem 15 supplies the global soundness estimate with exactly the squared-overlap convention used by I289. Its §2.1 induction handles large defects. Its technical role is old and explicit.

**Bae et al.:** the actual §§II–III, Lemma 5 proof, von Neumann remark (44)–(45), and Theorem 6 concern isotropic depolarizing tensor powers. They credit output-von-Neumann-entropy stability as an older goal. Their closest-product Taylor expansion, removal of weight-one perturbations and unspecified remainder do not provide the present GAD inequality or an n-uniform transfer. No verdict on that paper's validity is needed. I284's uniquely forced same-s postmap diag(1,1,s) has a negative Pauli coefficient, so it remains excluded.

**I280 and I288:** I280 pays (8), but not arbitrary productness. I288 only pays fixed-k stability through a finite core, with constants depending on k. Letting k grow in that result does not recover this target. I289 really completes unrestricted input stability on the claimed EB interval, and this review does not downgrade that scope to bounded k. The separate reduction (1)–(9), however, obtains that very scope from already established global tools and elementary operations.

**TECHNICAL** is therefore the contribution judgment under the unchanged standard requiring more than an elementary consequence of old or paid results. The exact additional connection is valid and useful: the same-tree quadratic test avoids selecting incompatible branch optimizers, and full-law rounding avoids adding n latitude errors. But the needed drift is already an immediate variance consequence of the old mixed-state test formula, and the latitude step is a metric/affinity calculation using the paid KL estimate. Neither requires a new tensorization principle, a new global soundness theorem, or control of an unbounded finite core. This is not a judgment based merely on shortness or the size of the EB interval.

The strongest case for SUBSTANTIAL is the removal of all phase complexity restrictions through a reusable EB argument. That is real project progress, and would matter more if the product-test formula did not support (3). Here the explicit stronger reduction shows that the structural payment follows from an already available quadratic representation with standard norm inequalities. I consequently do not classify this assembly as an independent substantial advance. This is an assessment of mathematical contribution, not proof invalidity or a claim of copied work.

## Priority and reporting limits

No inspected older paper literally states the displayed anisotropic GAD equatorial theorem. The reduction is this reviewer's deduction, and the author's/parent's bridge remains explicitly credited as shared input. An independently derived corollary is not evidence of an earlier publication. Literature priority remains unresolved; the bounded searches and four proof-level primary reads establish neither worldwide novelty nor an exact external duplicate.

Only the five assigned I293 paths are written. No subagents, other live sibling reads, shared-index edits, staging, commits, publishing, numerical scans or history replay occurred. Full external bodies were fetched in memory, not retained. Exact URLs, whole-body hashes, semantic read extents, input authentication and detached output hashes accompany the review.
