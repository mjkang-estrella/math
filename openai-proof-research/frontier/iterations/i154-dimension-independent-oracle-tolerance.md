# I154 — Original I152 audit and dimension-independent oracle tolerance

**A complete proposed proof of the explicit c_epsilon target is given below, under the stipulated source operations. It is submitted for independent proof and contribution review, not marked accepted. Eight accepted substantial findings remain eight.** The decisive finite-time regularization is an existing shifted-composition operation; the compiler constants and causal-state bookkeeping are the additional technical work. No substantial nomination is forced.

All OpenAI theorems and lower operations at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are premises. There is no upstream truth audit, contradiction inference, or ex-falso. External literature is ordinary evidence. No children, shared edits, staging, commits, or publication were used. Active I151/I153 are not dependencies. W152, H152, C145 and earlier parked branches remain parked.

## 1. Original audit, completed before continuation

The unchanged original I152 task has SHA-256 `f13a8eb19fe9ee8cdd1a6fbeb6618529a48c0599f08a84272be5b68570bf7379`. The full independent audit is frozen in [original-audit-report.md](../sources/i154_dimension_independent_oracle_tolerance/original-audit-report.md), with its pre-continuation [checkpoint](../sources/i154_dimension_independent_oracle_tolerance/original-audit-checkpoint.json). Its hash is `694f98b401ef41fd778c16a201496b6d105c1143ca48129d1c17875bd3647fa5`. The original report and verdict history have not been edited.

| Original claim | Verdict at its original scope |
|---|---|
| I148 inherited audit, including restricted A148 and conditional entropy | PASS without repairs; no extension to C145 |
| Conventional rational weighted-normalizer output lower bound; unchanged bin-method obstruction | PASS; compact answers and other sampling mechanisms are not excluded |
| Known independent nonidentical rank-bit correction | PASS at the positive-deletion efficient-decoder interface, with fixed known channel metadata |
| Actual hard-pair TV premise and Huber intersection | PASS for iid mixture contamination; no sharp deterministic-budget claim |
| R1, R3, R4 and standalone R2 | PASS at standalone invocation interfaces, including stateful errors, descent and finite-dimensional fallback |
| Literal assertion that every internal routine reserve is conditionally fresh and independent | **FAIL** for transformed internal seed arrays |
| Consistent-potential interpolation and nonconservative example | PASS; neither proves an adversarial-oracle impossibility |
| Dimension-independent R152 | Unresolved in original I152 |

The reserve failure is specific. A transformed mean child's seed covariance is `I-vv^T/(4D_s^2)`. Its internal anchor-sampler reserve can have nonzero shift coefficient, hence nonzero covariance with query-affecting slots. Merely drawing that coordinate later does not make it independent. Each **standalone top sampling call**, however, has an untouched final reserve, unused in every query in that call. That is sufficient for the paid R2–R4 interfaces and for this continuation. The correction here is separate; it does not erase the literal failure.

The audit includes actual coefficient interfaces, physical query shifts, duplicated expression nodes, fixed routine height versus expression depth, decoder wrong-prefix gap and correct-prefix PSD slack, bit lengths, small-deletion quantifiers, and the hard-pair proof ending. It preserves the original I133 I.5, I124 arbitrary-Q cutoff, I112 standalone G112, and I112 equal-zero-lambda scale-fixing failures. Original I148 retains ordinary classes, all signs/labels and actual volumes, conductor and discriminant direction, Mellin axis support, parameter order, fixed cutoffs, all-component restrictions, finite-scale entrances, and the invariant-lift gap. Details and actual read ranges are in the frozen audit and evidence manifests; a parent review is not substituted for this audit.

## 2. Exact theorem and conventions

**Theorem (proposed R154).** For every fixed epsilon>0 there are positive constants c_epsilon and C_epsilon and a randomized real-query algorithm with the following property. For every d>=2 and every C2 function V on R^d with supplied minimizer 0, V(0)=0 and I<=Hessian V<=2I, the algorithm makes at most C_epsilon d^epsilon value/gradient queries on **every execution** and returns a point whose law is within TV 1/10 of pi_V proportional to exp(-V). At each queried x the replies may be arbitrary subject to

    |Vhat(x)-V(x)| <= c_epsilon,
    ||ghat(x)-gradient V(x)||_2 <= c_epsilon.

Replies may depend measurably on all past queries and replies and on the current query, with arbitrary private adversary randomization, but not on future private algorithm draws. No common approximate potential, unbiasedness, continuity or differentiability of errors is required.

As usual a randomized oracle strategy is a measurable causal kernel; otherwise an output probability law need not exist. Finite real query/reply histories form standard Borel spaces. This is a real-query theorem with unrestricted intervening computation. It asserts neither finite-bit complexity nor arbitrary-accuracy amplification. Constants may depend on epsilon. The original R152 prose left the error-constant/epsilon order unspecified; this theorem does **not** establish a single positive c working for every epsilon.

We use TV=one half of the L1 distance, KL(P||Q)=integral log(dP/dQ)dP, and Euclidean W2. The letter eta below denotes the original gradient-error tolerance; the source routine's reserve parameter is written s to avoid confusion. Source parameters K0,t,w and numerical approximation orders are fixed before dimension thresholds. The symbol B_d denotes a fixed power of 1+log d, allowed to change a fixed number of times. Constants denoted C_* depend on these fixed parameters, never on d,V,centers,seeds or the adversary.

## 3. Constant fixed-seed compiler stability

The operative source is the complete numerical interface and compiler (`numerics.tex`, `implementation.tex`), not an abstract recurrence substituted for that compiler. Terminal calls are

    M(x,r,sigma)=g(x+rZ)+sigma G,
    S_pre(x,r,s)=Z-r g(x+rZ)+(sqrt(3)s/2)G1.

Their fixed-seed center Lipschitz constants are lambda and r lambda; an error of size u in g changes the outputs by at most u and ru. All reachable r<=1 and lambda<=delta. Nonterminal center expressions have direct term x+r(ell y+mG), with bounded ell,m; their absolute mean-coefficient sum is A. The final sums are bounded by C1 for M and C1 r for S. The M final direct term is independent of its position anchor; the S direct anchor is a fixed Gaussian seed. Child scales r tau do not exceed r (and satisfy the source lower scale bound). Seed transformations and scalar coefficients are independent of oracle responses and centers.

The routine height H=H(K0,t) is fixed. The finite expression depth D0 is distinct from H. Every duplicated occurrence in the uncached expression expansion is a direct child of its parent routine, including its center-supplying tree. Thus an absolute row-sum estimate applies separately at every expression tier; no factor equal to the number of occurrences is inserted. For every reachable call, the source size calculation gives

    lambda A <= B_d delta^(1/3).                                      (1)

Here is an explicit simultaneous induction sharpening the source's allowed polylogarithmic stability bound. Choose C>=max(2,C1) also bounding every fixed direct coefficient. Put L0=P0=1, and for k=1,...,H define

    Lk=8 C^2 L_(k-1)(1+L_(k-1)),
    Pk=8 C^2 P_(k-1)(1+L_(k-1)).                                      (2)

Only after these constants are fixed choose d large enough that `max_k Lk lambda A<=1/2` in every reachable call. Equation (1) permits this uniformly. Increase this threshold to meet the source scalar-size conditions.

At height k, hold position anchors fixed first. For two exact runs, put v=|Delta x|+C r|Delta anchor|. At an expression node its supplied-center discrepancy is at most

    v+A L_(k-1) lambda max_(earlier occurrences) E.

Induction through the acyclic expression tree bounds E by 2v, regardless of how many nodes occur. The final expression then has sensitivity at most `2 A_f L_(k-1) lambda v`. In M the anchor itself is a lower-height S output multiplied by b_*<=1. Its center sensitivity is at most `L_(k-1) r lambda`. Consequently the additional M sensitivity is at most `2 C^2 L_(k-1)^2 lambda^2 r^2`, bounded by the chosen Lk lambda since lambda r^2<=1. The M sensitivity to an externally supplied position anchor is at most `2 C^2 L_(k-1) lambda r`. The S Gaussian anchor is unchanged. The factor C^2 in (2) covers these direct and final coefficients. Thus exact M and S_pre have center Lipschitz bounds Lk lambda and Lk r lambda for **every fixed seed array**, including transformed arrays.

Now compare arbitrary erroneous and exact runs with the same fixed seed list. A child comparison is split into erroneous versus exact at the erroneous center, then exact at the two centers. This uses only the true child's Lipschitz bound; it never assumes regularity of erroneous replies. With parent anchor discrepancy Delta a, center discrepancies satisfy

    E <= C r|Delta a|+A P_(k-1)u
                       +A L_(k-1)lambda max E_previous,

and hence `E<=2(C r|Delta a|+A P_(k-1)u)`. At the final expression the error is bounded by

    A_f P_(k-1)u
      +2 A_f L_(k-1)lambda(C r|Delta a|+A P_(k-1)u).                 (3)

For S the anchor discrepancy is zero and A_f<=C r. For M the anchor S has error at most P_(k-1)r u, and A_f<=C. Absorption of L_(k-1)lambda A and lambda r^2<=1 gives (2)'s Pk bounds with C fixed as above. Therefore

    |Mhat-M| <= C_* u,
    |Shat_pre-S_pre| <= C_* r u.                                    (4)

Every changed physical terminal query is paid by the exact gradient Lipschitz comparison above. Repeated queries may receive different errors, and duplicated subtrees may have different histories. The estimate holds for each such collection of bounded errors and every seed list. No internal reserve independence or Gaussian absorption is used for the erroneous run. The source's absorption and moment arguments continue to apply only to the exact comparison compiler.

## 4. Fresh-reserve entropy and state retention

For a standalone primitive invocation draw all seeds used in its queries first, and draw its final sG/2 only after those calls. This changes no exact standalone distribution. A causal adversary cannot use that future reserve. Conditional on the incoming history, couple the exact and erroneous pre-reserve outputs using the same earlier seeds and, if needed, an independent seed representation of the adversary's conditional kernels. The reserve is independent of this entire latent variable.

If two latent-dependent centers a,b satisfy |a-b|<=D and independent N(0,vI) is then added, joint convexity/data processing for KL gives

    KL(Law(a+sqrt(v)G) || Law(b+sqrt(v)G)) <= D^2/(2v).             (5)

Indeed retain the common latent variable in both experiments, use the Gaussian translation identity conditionally, integrate, and then discard that variable. This needs no differentiability of a,b and makes no claim about oracle transcript closeness.

In an outer transition put h=delta/2 and `g_y(z)=sqrt(h) gradient V(y+sqrt(h)z)`. The normalized oracle error is u=sqrt(h)eta. At r=s=1, (4) and the final physical rescaling give displacement at most C_* h eta and reserve variance h/4. Hence, conditional on every incoming adversary history,

    KL(noisy compiler output || exact compiler output)
       <= 2 C_*^2 h eta^2.                                         (6)

This compares to the **exact compiler**, not to its ideal target kernel. Its intrinsic approximation error is charged later.

For clarity the state replacement used here is a measure-theoretic operation, not a transcript simulation. Let s denote the incoming enlarged state and let a completed transition have joint kernel

    K_s(dz,ds')=k_s(dz)L_s(z,ds').

A jointly measurable regular conditional kernel L exists on standard Borel spaces. Define it arbitrarily as a fixed probability kernel on any exceptional set. For any replacement marginal e_s set `E_s=e_s L_s`. If k_s<<e_s, the joint Radon–Nikodym derivative is dk_s/de_s at z, so

    KL(K_s||E_s)=KL(k_s||e_s),
    TV(K_s,E_s)=TV(k_s,e_s).                                        (7)

Projection gives the reverse inequality if one first proves the upper bound by integration. Gaussian output mixtures have everywhere positive densities, so here the noisy and exact visible marginals are mutually absolutely continuous; exceptional versions cannot change either joint law on their relevant support. For other ideal replacements the arbitrary extension still defines a probability kernel, and the TV identity remains true without absolute continuity. Kernels are defined for every possible finite history; extensions on unreachable histories can always use an admissible bounded reply.

Repeat (7) along a finite chain, replacing each visible marginal by the exact compiler marginal while retaining the actual conditional next-state kernel at that incoming state. The replacement process has the exact compiler visible transition conditional on its **whole** past, irrespective of its auxiliary state. The conditional KL chain rule, from the identical initial joint law, and data processing imply for a window of m calls

    KL(actual window joint law || replacement window joint law)
       <= 2 C_*^2 m h eta^2,
    TV(actual endpoint, exact-compiler endpoint) <= C_*eta sqrt(mh). (8)

Here the joint law records visible outputs and carried states, not both inconsistent exact and actual transcripts. No full-transcript likelihood comparison is asserted. The kernel L may encode the actual transcript; it is deliberately retained in both laws. This construction also justifies incoming-variable TV replacement and ideal-prefix moment arguments in the final conditional descent.

## 5. Fixed-time regularization of the actual ideal noised proximal kernel

Define `kappa_y(dx) proportional exp(-V(x)-|x-y|^2/(2h))dx` and `P_h(y)=kappa_y*N(0,hI)`. The source proves invariance of `pi_tilde=pi_V*N(0,hI)` and W2 contraction with q=(1+h)^(-1), including `W2(kappa_y,kappa_z)<=q|y-z|`. Coupling those conditional draws and using Gaussian mixture KL gives

    KL(P_h(y)||P_h(z)) <= q^2 |y-z|^2/(2h).                         (9)

For all finite-second-moment input laws and integers m>=1,

    KL(mu P_h^m || nu P_h^m) <= W2(mu,nu)^2/(2hm),
    TV(mu P_h^m,nu P_h^m) <= W2(mu,nu)/(2sqrt(hm)).                  (10)

Here is a full discrete proof. It is the nonexpansive specialization of the existing shifted-composition regularization argument, reproduced to specify all h dependence. Set mu_j=mu P_h^j, nu_j=nu P_h^j, and auxiliary rho_0=nu. Couple X~mu_j and Y~rho_j optimally in W2, take theta_j=1/(m-j), set Z=Y+theta_j(X-Y), and let rho_(j+1)=Law(Z)P_h. These couplings exist for finite-second-moment laws; only finitely many deterministic laws are involved. Their disintegrations are measurable, with arbitrary probability extensions on null sets. With a_j=W2(mu_j,rho_j), contraction and the displayed coupling give

    a_(j+1)<=q(1-theta_j)a_j,
    a_j<=q^j (m-j)a_0/m,
    rho_m=mu_m.                                                     (11)

Let K_j(y) be the mixture of P_h(Z) given Y=y in this coupling. The ordinary joint KL chain rule for rho_j(dy)K_j(y,dz) versus nu_j(dy)P_h(y,dz), followed by projection, implies

    KL(rho_(j+1)||nu_(j+1))
       <= KL(rho_j||nu_j)+integral KL(K_j(y)||P_h(y))rho_j(dy)
       <= KL(rho_j||nu_j)+(q^2/(2h))theta_j^2 a_j^2.                (12)

The last inequality is mixture convexity and (9). Starting with zero KL, (11) makes the sum at most `(q^2/(2h)) a_0^2 m^(-2) sum_(j<m)q^(2j)<=a_0^2/(2hm)`. At the final step rho_m=mu_m, proving KL in (10); Pinsker proves TV. Positive transition densities and the finite bound inductively ensure the required absolute continuity. This proof uses a finite sequence of measurable kernels and does not need a continuum diffusion, an implementable optimal coupling, or an exact-score identity for the erroneous oracle.

In particular m=ceil(1/h) yields TV<=W2/2 uniformly in d and h. One-step regularity alone would lose h^(-1/2); (10) distributes the shifts across the window. This is **already an existing stability operation**, not a newly invented log-Harnack theorem. [Altschuler–Chewi, Shifted Composition I, Theorem 3.2, Remark 3.4 and §3.3](https://arxiv.org/abs/2311.14520) prove a sharper contraction-dependent version; the operative proof and convexity extension were read through their endings. Their [Shifted Composition III, §3.1](https://arxiv.org/abs/2412.17997) develops the related comparison of different kernels.

## 6. Algorithm and complete error accounting

Fix 0<e<min(1,epsilon/2), put delta=d^(-e), h=delta/2, choose integer K0>2+1/e, then choose t,w and approximation orders in the source-prescribed order. In particular e(1+t)<epsilon. Fix H and all constants in (2), then the uniform large-dimension threshold. Throughout take 0<=eta<=1.

**Warm-up.** Start at y=0 and run T=ceil(C h^(-1)log d) noisy compiled outer transitions. All loops have fixed lengths. Combining (4) with the source intrinsic local W2 error gives, for a_j=W2(actual visible law,pi_tilde),

    a_(j+1) <= (q+2h B_d delta^K0)a_j
               +C sqrt(h)B_d delta^K0 sqrt(d)+C_* h eta.            (13)

This holds with adversary state retained: condition on the current state, use the same-seed noisy/exact coupling, then the exact compiler/ideal coupling, and integrate against an input coupling. Since RMS(y)<=a_j+C sqrt(d), moments remain finite at each step. The coefficient is at most 1-c0 h for large d. Thus

    a_T <= C sqrt(d)exp(-c0 hT)
              +C h^(-1/2)B_d delta^K0 sqrt(d)+C_*'eta
         = o(1)+C_*'eta,                                           (14)

uniformly over V and all allowed strategies. The intrinsic remainder is actually o(sqrt(h)) with these parameters. Write mu for this warm-up visible law, retaining its joint law with the adversary state.

**Entropy window.** Append m=ceil(1/h) noisy compiled transitions. Bound (8) compares their visible output to mu Phat_h^m with cost at most C_*eta sqrt(1+h), where Phat_h is the exact compiler. Compare this to mu P_h^m separately. The source intrinsic TV bound is

    TV(Phat_h(y),P_h(y))
       <= B_d delta^K0(sqrt(d)+2sqrt(h)|y|).                         (15)

Use a hybrid with an ideal prefix and exact-compiler suffix. Under every ideal prefix from mu, contraction and (14) bound RMS(y) by C sqrt(d)+C_*'eta+o(1). Therefore the sum of (15) is bounded by

    C m B_d delta^K0(sqrt(d)+sqrt(h)C_*'eta)
       <= B_d delta^(K0-1)(C sqrt(d)+C_*'eta)=o(1).                 (16)

It is important that (16) is a TV comparison of the exact compiler to the ideal kernel; (6) was not silently strengthened to compare to that ideal kernel in KL. Apply (10) to mu and invariant pi_tilde, then (14). Together,

    TV(actual window endpoint,pi_tilde) <= C_*''eta+o(1).           (17)

All uniform remainders can be chosen simultaneously for 0<=eta<=1. No errors are telescoped in TV across the noisy window: its oracle error was summed in KL.

**Conditional descent.** Replace the incoming visible y by pi_tilde using (7), retaining the actual conditional adversary-state law. This costs (17). Use the original fixed J=ceil(C1 log d) variance-halving descent, with r_j=2^(-j/2), fresh standalone primitive calls, and the same normalized oracle g_y throughout. At level j, (4) and the fresh final reserve of standard deviation 1/2 give an additional conditional TV error at most C_*r_j sqrt(h)eta. Its sum is at most C sqrt(h)eta. For intrinsic errors, perform history-by-history joint-state TV replacements with ideal prefixes. The visible ideal process conditional on the full preceding state has the stipulated ideal law. Thus the source bound `E|g_y(x_j)|^2<=Cd` remains valid, and the sum of intrinsic errors is `C J B_d delta^K0 sqrt(d)=o(1)`.

At the terminal mode iteration, compare the noisy iteration to the exact contraction, rather than differentiating its errors. Its additional center error is at most

    r_J sqrt(h)eta/(1-delta r_J^2).                                 (18)

The final standard Gaussian translation pays this in TV. The exact mode-iteration and mode-centered Gaussian approximation errors are the source's o(1), with the same deterministic iteration cap. The returned point is y+sqrt(h)(x_J+r_J Z_J), so data processing cannot increase these conditional TV bounds. This proves

    TV(output,pi_V)<=C_e eta+o(1).                                  (19)

All state replacements have finite horizons and standard Borel disintegrations as in §4. They do not condition a putatively independent exact trajectory on future success. An inconsistent oracle is used only via its pathwise uniform error.

**Every-run query count and small dimensions.** The source count for warm-up, fixed descent and mode iteration is at most `B_d delta^(-(1+t))`. The m added calls cost at most the same order (the warm-up already has order h^(-1)log d calls). All circuit sizes, expression expansions, and loops are prescribed before replies, so the bound holds on every execution, including extreme Gaussian seeds and malformed-but-bounded numerical reply histories. Since e(1+t)<epsilon, this is at most C_epsilon d^epsilon for all sufficiently large d.

First choose c_epsilon<=1 so that C_e c_epsilon<=1/40, then choose a dimension threshold so the uniform remainder in (19) is <=1/40. For the finitely many 2<=d below that threshold use the source capped rejection algorithm: independent X~N(0,I), and accept with probability

    exp(-Vhat(X)+|X|^2/2-c_epsilon).

It is between exp(-2c_epsilon) and one times the exact acceptance, and never exceeds one. The exact acceptance probability is at least 2^(-d/2). With L_d=ceil(4*2^(d/2)) trials, failure costs at most exp(-4). Couple accept/reject uniforms with the exact capped algorithm; at each trial the extra disagreement probability is at most 2c_epsilon even conditional on past adversary state. Decrease c_epsilon to make `2 max L_d c_epsilon<=1/40`. The total fallback TV is below 1/10. Increase C_epsilon to pay every finite cap. The finite-dimensional fallback uses values; the main algorithm uses gradients only. This completes the proposed theorem.

## 7. Comparison, Route B, and contribution gate

The closest general mechanism is the existing shifted-composition regularization, not unbiased stochastic-gradient concentration. Theorem (10) is a direct instantiation, and the Gaussian-mixture KL identity plus finite-horizon chain rule are standard. The compiler-specific content is (4), including anchors and transformed/duplicated calls, and its integration with causal joint-state replacement and the source's ideal-prefix moment and deterministic-cap interfaces. The resulting theorem is stronger than original R4, but a stronger consequence is not automatically a substantial new finding. **Treat this as a completed proposed technical deduction under the supplied machinery, pending independent proof and contribution gates; no acceptance is claimed.** A contribution case for review is the complete arbitrary causal inconsistent-oracle model at subpolynomial every-run cost, rather than a new entropy inequality. A negative contribution case is that once the source compiler is inspected, constant stability plus known regularization is routine source composition. No worldwide absence or priority claim is made.

[Dalalyan–Karagulyan, arXiv:1710.00095v4, Condition N and Theorem 4](https://arxiv.org/abs/1710.00095v4), permits biased, temporally dependent errors with a fresh independent Gaussian update. Its operative proof, fundamental coupling recursion and required lemma endings were read. With a Euclidean error bound eta, conditional bias and residual second moments are at most eta and eta^2; one may take delta=eta/sqrt(d), sigma<=eta/sqrt(d) in its notation. A deterministic history-dependent error need not have zero conditional variance given only the current position. Its bias floor is dimension independent, while its Euler discretization term is proportional to sqrt(hd). Thus this existing stability result does not supply the requested subpolynomial every-run query cap. No statement that robustness requires unbiasedness is made.

For intuition only, an adapted bounded drift perturbation b_t in Langevin dynamics has finite-horizon path entropy bounded by one quarter of E integral |b_t|^2 dt under the usual Brownian variance-two convention, and synchronous strong-convexity comparison gives an O(eta) Wasserstein floor. A fixed-time final window therefore has the same scaling as (8)–(10). This continuum observation is not offered as a second algorithm: a finite-query discretization must still be paid. The theorem above supplies that realization using the stipulated compiler. No indistinguishability obstruction in the prescribed-mode, two-oracle-error model was found. The mode-preserving rotational example only excludes consistent-potential interpolation.

[Chen–Chewi–Daskalakis–Rakhlin, PMLR 336 (2026)](https://proceedings.mlr.press/v336/chen26g.html) has iid unbiased light-tailed oracle interfaces. The complete relevant FORS, Gaussian tilt, technical and proximal comparison proofs were inspected at the recorded ranges. They are not the causal bounded-bias interface used here. [Smoothed Picard HMC, 2609.06906v2](https://arxiv.org/abs/2609.06906v2), has exact-gradient interfaces, expected query bounds, fixed-seed stability and an explicit approximate-proximal-center stability operation. Appendix D's full error/certificate/expected-work proof and Appendix E's arbitrary-depth exact-smoothed-gradient proof were read through their endings. Approximate proximal centers do not themselves authorize arbitrary inconsistent gradient answers. The existing finite-depth and small-coefficient ideas substantially narrow the contribution claim. No whole-companion-proof read is claimed where only a nonapplicability statement was used.

[Gaussian cloud correction, 2609.38710](https://arxiv.org/abs/2609.38710), Theorem 1.1, gives an expected gradient-query bound with dimension exponent 1/5 under its exact-gradient interface. Only that complete operative statement was read; its whole likelihood-correction proof is not claimed read or used. The [June 11, 2026 journal version of Shifted Composition III](https://doi.org/10.1007/s10208-026-09753-x) was separately retrieved and its complete Section 3.1 read through the proof ending, including its clarification that auxiliary variables may be recoupled after their marginals are specified. Our regularization proof uses only the zero-local-error, nonexpansive case and supplies its own shift schedule, so no unread general-L optimization or weak-error theorem is invoked. Current-version and retrieval records are in the evidence directory. A retrieved preprint and a later journal record are not silently identified byte-for-byte. Search-only results are not relied on as mathematical premises.

## 8. Evidence and verification limits

The mandatory task's entire decoded stream and recursively required decoded records were read through their endings; recovered truncations are recorded separately. The original complete 13,223-entry / 749-manuscript / 10,373-original-position map and 776 PDF/text bindings are reused through one flat preparation traversal, with exact lexical multisets and positions. This is lexical/evidence coverage, not a claim to have semantically read all manuscripts. No corpus was copied, no inherited PDF was re-extracted, and no ancestor verifier or diagnostic was run. Current ledgers were snapshotted; those four live ledgers alone may drift.

The owned inventory is canonical and prevalidated before one exclusive-create seal. The offline verifier checks immutable owned, inherited, context, corpus, lexical, primary and passage bytes before running only the new finite diagnostics. Its audit hook denies network, subprocess, writes and bytecode-producing mutation; it cannot repair or reseal. Finite diagnostics and evidence reproduction do not certify the universal proof, substantial contribution, acceptance, priority, or human/formal correctness.

Run from the project root:

    python3 -B frontier/experiments/i154_dimension_independent_oracle_tolerance/verify.py

The full theorem above is the output for later independent gates. The stronger single-c-for-all-epsilon formulation remains unproved. W152, H152, C145 and earlier parked branches remain parked. **Eight accepted, two remain.**
