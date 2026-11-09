# Independent preliminary review: dependent super-coupon cover time

Recommendation: **retain the ordinary proof; HOLD acceptance/counting pending novelty and formal gates.** No fatal mathematical gap or counterexample found. This review is independent and solo; optional root triage was not used. Root alone accepts or counts. Administrative snapshot: 9 additional, 39 total, next 40; unchanged.

## Explicit verdicts

| Gate | Verdict | Exact limitation |
|---|---|---|
| SOURCE | PASS for arXiv:2304.01145v2 Conjecture 2.4 | Actual statement and relevant proof bodies read. Published-version correspondence and citing-body history remain open. |
| MATH | PASS, ordinary mathematical proof | All fixed integers 1≤s≤r, n→∞, uniform OLD-complement swaps; expected full cover time only. No growing parameters or Gumbel conclusion. |
| SUBSTANTIVE | Provisional PASS for further investigation; no automatic exclusion demonstrated | Distinguished-union killed chain plus quantitative relative pair tails is a genuine model-specific bridge. All tools are classical; root must adjudicate campaign substantive credit after prior-art clearance. |
| NOVELTY | HOLD / not established | No complete same-model prior subsumer identified in the bodies examined, but registry, journal and citer gaps prevent novelty clearance. |
| FORMAL | NOT READY; feasibility plausible, cost material | No Lean endpoint or strict replay exists. Finite-chain probability, spectral perturbation and asymptotic infrastructure must actually be supplied. |

## Source and scope

The target is Siva Athreya, Satyaki Mukherjee and Soumendu Sundar Mukherjee, *On a generalisation of the coupon collector problem*, [versioned primary PDF](https://arxiv.org/pdf/2304.01145v2). Conjecture 2.4 begins on PDF p4 and finishes on p5, including its formula. Given H_t, it replaces a uniform member of H_t by a uniform member outside H_t. The claimed mean is

E T ~ (r/s) binom(n,s)/binom(r,s) log binom(n,s).

The candidate's fixed-r,s interpretation is correct. Its proof is not an extension to growing r or s. The source's iid Gumbel theorem is a different result. The source already proves r=s in Theorem 2.5; that boundary is verification, not a new discovery. Also s=1 has the elementary exact transition-count mean (n−r)H_(n−r): when k coupons remain unseen, the next added coupon is unseen with probability k/(n−r), independently of which old member was deleted. Thus the prospective unresolved contribution is the full regime 2≤s<r, within one family.

Current arXiv target page was lawfully retrieved 2026-10-30 14:41:32 UTC, HTTP 200. It identifies v2 as latest: v1 submitted 2023-04-03 17:11:31 UTC, v2 2023-09-12 17:25:49 UTC. The v2 PDF title page independently says 12 Sep 2023. These are preprint chronology facts; they do not authenticate a journal version, establish journal correspondence, or prove no later resolution elsewhere. No journal body was retrieved here.

## Independent mathematical audit

Put N=binom(n,s), p=binom(r,s)/N and q=sp/r. All O-constants below depend only on fixed r,s.

**Lumping, independence and feasibility.** For W=S or S∪U, with m=|W|≤2s, B=H∩W is a sufficient state. The fixed feasible space is all B⊆W with |B|≤r when n≥m+r. Given H, the deleted member and the added OLD-complement member are independent uniform choices. The added distinguished member must lie in W\B, including after a distinguished deletion; permitting the deleted member to be re-added would change the model. Outside deletion has probability (r−|B|)/r, outside addition (n−m−r+|B|)/(n−r). The latter count is independent of which old member is deleted. Multiplying these probabilities gives the four transition types in PROOF.md, including simultaneous distinguished deletion/addition and the self-loop from two outside choices. Zero-probability branches at |B|=r must simply be ignored. The rational checker independently compares this matrix against enumeration of every original H in its finite test cases.

**Stationarity and reversibility.** The weight for a SPECIFIC state B is binom(n−m,r−|B|)/binom(n,r); there is no binom(m,|B|) factor until aggregating by cardinality. A full H swap has reverse swap probability 1/[r(n−r)], so uniform r-sets are reversible and the lumped weights satisfy detailed balance. They sum to 1 and π(∅)=1−O(1/n). This justifies the exact flow calculation, rather than merely a plausible entry-rate heuristic.

**Zero-limit spectrum and perturbation.** With z=1/n, every entry is a rational analytic function near 0. At z=0 only distinguished deletion survives. D consists of sets containing neither full target and is downward closed. Thus K(0) has row sums 1, and, in increasing cardinality order, is triangular with diagonal 1−|B|/r. Only ∅ has diagonal 1, so its algebraic multiplicity is exactly one. Every other diagonal lies in [0,1−1/r]. This proves simplicity without an irreducibility assumption and also handles unions larger than r. No Jordan assumption is needed.

Choose ρ strictly between 1−1/r and 1. Shrinking a complex z-neighborhood makes both the contour around 1 and |w|=ρ disjoint from the spectrum. The finite-matrix resolvent is bounded there by compactness and the adjugate/determinant formula. The Riesz projection Π is analytic and rank one, Π(0)1=1. Dividing Π(z)1 by its ∅ coordinate yields f(∅)=1 and f=1+O(z) uniformly, hence f>0 for small positive z. Reality follows from conjugation and uniqueness of the nearby eigenvalue. Cauchy's power formula on |w|=ρ gives K^t−λ^tΠ=O(ρ^t), uniformly in integer t≥0 and small z. It absorbs all polynomial factors from possible Jordan blocks. The proof's brief complementary-resolvent phrase is valid with this precise interpretation.

**Exact eigenvalue/flux identity.** Extend f by zero on A. Detailed balance gives

Σ_(x∈D) π_x(Kf)(x) = Σ_(y∈D)π_y[1−P(y,A)]f(y).

Subtract λΣ_Dπ f to obtain exactly

(1−λ)Σ_Dπ f = Σ_D π_x P(x,A)f(x).

The denominator is 1+O(z), since π(A)=O(p); positivity and f=1+O(z) make the numerator Q(D,A)(1+O(z)) RELATIVELY, even though Q is order z^s. This is the crucial feature: generic absolute O(z) eigenvalue control would be inadequate when s>1. Also a=π_DΠ1=1+O(z), so stationary avoidance through times 0,...,t is aλ^t+O(ρ^t).

**One and pair rates.** For one target, deleting a member of S destroys S with probability s/r, and it cannot be immediately restored. Hence Q(A_S,D)=p s/r=q exactly. For distinct S,U, let I=A_S∩A_U. Its mass is zero if |S∪U|>r; otherwise it is binom(n−|S∪U|,r−|S∪U|)/binom(n,r)=O(p/n). Write X=A_S\A_U and Y=A_U\A_S. Expanding both flows shows that [exit flow of A_S]+[exit flow of A_U]−[exit flow of their union] is exactly

Q(X,Y)+Q(Y,X)+Q(I,D)+Q(I,X)+Q(I,Y).

In particular it is nonnegative and ≤2ps/(n−r)+π(I) (even the candidate's more generous intersection bound suffices). An X→Y jump must add a missing U member; a uniform OLD-complement addition has probability ≤s/(n−r). Thus the union flow is 2q+O(p/n). The resulting eigenvalue deficits are q(1+O(1/n)) and 2q(1+O(1/n)). There are only s distinct pair-overlap types, so take maxima of all contour, eigenvector and flow constants. No sum over a growing number of different constants is hidden here.

**Relative tails at cover time.** At t=floor(θ log N/q), fixed θ>0, log λ_1=−q+O(q/n+q²) and log λ_2=−2q+O(q/n+q²). Multiplication by t gives errors O(log n/n+q log n)=o(1). The amplitudes tend to 1. Since q is Θ(n^−s), ρ^t is negligible even after division by N^−2θ. Thus the one/pair probabilities are N^−θ(1+o(1)) and N^−2θ(1+o(1)), uniformly. This is enough relative accuracy for ALL pairs, including disjoint pairs and maximally overlapping distinct pairs; a weak exponential limit alone would not be.

**Second moment and mean tail.** At θ=1−ε, EM=N^ε(1+o(1)), E[M(M−1)]/(EM)²→1, and Var(M)/(EM)²→0. Chebyshev gives P(T>t)→1, hence liminf ET/(q^−1 log N)≥1−ε. For the upper bound, the uniform all-t survival inequality Cexp(−αt)+Cρ^t with α=q(1−C'/n)>0 yields a union bound. With t0=ceil((log N+sqrt(log N))/α), summing the first tail is O(exp(−sqrt(log N))/α), using 1−e^−α~α. The second is O(Nρ^t0)/(1−ρ), also negligible. t0/(q^−1 log N)→1. These estimates prove the mean asymptotic, including uniform integrability rather than only a high-probability assertion.

**Initial state and indexing.** The full cover statistic is invariant under every relabeling, and relabelings act transitively on deterministic r-set starting states. Therefore its distribution from any deterministic H0 equals its stationary-start mixture. Individual target probabilities need not enjoy that transitivity, but they are only used AFTER switching the cover statistic to stationary start. If τ is the first hit at index ≥0, {τ>t} is avoidance at 0,...,t and is π_D K^t1. The cover index and the source's number of rounds differ by one, irrelevant on the diverging scale. For r=s=1, D={∅}, K_single=1−1/(n−1), K_pair=1−2/(n−1), with stationary amplitudes (n−1)/n and (n−2)/n. This checks the delicate r=1 degenerate case directly. For r=s, all containing-target states are single full targets; the same reasoning remains valid and agrees with the already proved source theorem.

No repair of the candidate's scientific proof is required by this audit. The expanded derivations above make its compact steps reviewable.

## Strongest classical objection and its limits

Actual target-source proof bodies read: Lemma 3.2/Corollary 3.3 and Theorem 2.1 proof, PDF pp8–10; Matthews statement and r=s overlap recurrence, pp13–15. The iid proof already has the missing-count second moment, relative log-time comparisons, and summed expectation tail. The r=s argument already lumps overlap with a distinguished target, obtains a three-term recurrence, and applies vertex-cover Matthews. Extending its single-target birth–death recurrence to s<r gives mean hit time ~1/q. That alone does not give the cover constant: targets are overlapping sets of r-states, and Matthews' vertex theorem does not directly apply. A disjoint-target selection has only order n targets and loses the required logarithmic factor s. Candidate discovery.md correctly identifies this obstruction.

Actual older primary bodies inspected:

* [Keller, 1202.3900v1](https://arxiv.org/pdf/1202.3900v1), §2 assumptions (1)–(6) and perturbation theorem, REPFO definition, §3.1 formulas (15)–(22), §3.2 Proposition 2 and its proof (PDF pp2–8). It supplies the spectral/escape-rate architecture AND a quantitative exponential-tail estimate. It must not be dismissed as only weak convergence. In particular its (15) is already a spectral-power survival formula. However the paper's REPFO specialization has a fixed underlying dynamical system and shrinking holes. Our original Markov spaces grow with n; the useful fixed-space reduction has n-dependent un-killed dynamics and limiting stationary mass concentrated at ∅. Directly mapping Keller's fixed reference P0 and hole-size Δ to K(0) fails: δ_∅(K(0)−K(z))1 can even vanish to first order for s>1, whereas the real loss is order z^s. A valid application would need a suitable family embedding, verified operator hypotheses and quantitative single/pair rate calibration with error o(1/log N). The candidate supplies an independent finite analytic/flux bridge instead. Keller's generic 1−λ=θμ(A)(1+o(1)) by itself cannot be exponentiated at q^−1 log N. Even its quantitative Proposition 2 does not calibrate ξ_ε to s/r at that precision without additional model work. No complete direct same-model subsumption is exhibited here.
* [Abadi–Saussol, 1003.4856v2](https://arxiv.org/pdf/1003.4856v2), Theorem 1 statement (p3), Theorem 7/Lemma 8 and full main hitting approximation proof (pp5–7). Theorem 7 gives a uniform ABSOLUTE approximation bounded by a square-root expression in short hitting probability and α-mixing, with an unspecified normalizer λ(A). It does not identify the present q or give a relative pair approximation on a tail of order N^−2θ. Even an optimistic block length L=O(log n), error on the scale sqrt(Lp) is much larger than N^−2θ near θ=1; merely quoting this bound cannot run the required second moment. The theorem's fixed-process quantifiers also require a justified triangular-family application. This does not exclude stronger results elsewhere in that literature.
* A new bounded lawful search for “coupon collector” Markov returned 11 title entries. One broad coverage candidate was followed to its actual body: [Aldous, 2101.12671v1](https://arxiv.org/pdf/2101.12671v1), PDF pp1–6, §2.1 random-subset Proposition 2, §3.1 monotonicity Proposition 4, and their application proofs. Proposition 2 assumes independent successive random sets; our successive collections are dependent. Proposition 4 is a concentration bound under strong monotonicity of expected remaining hit times, not a formula for the expectation or log-time pair tails. Neither body supplies the missing leading constant in this model. The other ten search items were title/abstract screening only, not exclusion evidence from actual proofs. Search coverage is finite and keyword-dependent.

Assessment: the proof is an intelligible classical assembly, and the strongest objection is substantial enough to disclose. Nevertheless no explicit full same-model theorem application with the necessary rates and relative logarithmic-time pair bounds has been found. Using standard tools is neither an automatic discovery credit nor an automatic exclusion. Provisional substantive retention is warranted; a claim of demonstrated nonroutine new-to-literature mathematics is not yet warranted.

## Formal feasibility

Only an assessment is given. Main potential cost is connecting a finite Markov path probability to killed-matrix powers, a uniform complex resolvent/Riesz projection or equivalent algebraic perturbation theorem, positivity and stationary-flux identities, quantitative asymptotics, and expectation as a tail sum. A real finite-dimensional algebraic/recurrence replacement for contour theory may reduce library dependence; it must still prove a uniform exponential remainder. A single-target mean-hit calculation or a formal finite checker would not constitute the endpoint. No Lean/manuscript was created or modified, and no formal timing estimate or guaranteed low-cost path is asserted.

## Provenance, body coverage, access and diagnostics

All scientific inputs were frozen before scientific reading by freeze.py under the assigned external helper_guard.py, at 512MiB address space/group RSS, CPU210s and wall230s; required thread/environment settings were used for every Python/helper/retrieval/hash operation. bindings.json records original/copy/before SHA256 for 49 immediate candidate/evidence/primary/text files; this is not a recursively copied historical evidence tree. Only the three relevant primary source passages above were scientifically read from that cached set. Other frozen primary files are NOT claimed as body coverage. Administrative files were snapshots only. The ancestor and batch AGENTS.md were read; administrative ledger/context were parsed in full, with initial truncated display explicitly preserved as a limitation. Optional root triage was not consulted. No upstream theorem from the OpenAI collection is used.

Key SHA256 values:

| Input | SHA256 |
|---|---|
| Candidate PROOF.md | 35dd4276636707f555059a8584d98e6b30e18404c09b104030c5b666e957e22b |
| Target 2304.01145v2 PDF | 352d8326972d723df20f168f8ab8719fe485d910ca1a0d9b27ac9d7f22d1ce21 |
| Keller 1202.3900v1 PDF | d54c17c353b52ddf4dc34c6ad086ade89a826102885e670a999cda896c30410f |
| Abadi–Saussol 1003.4856v2 PDF | f4a0ccfef0ba4db3bf947c9b4d5125f6b577d5a3b92d3eb9e6350f3b92dfe0fb |
| Aldous 2101.12671v1 PDF | 1e1ebff338cc4624d2d06ee660d64fdd823d9e51b552010228731296eec3e3de |

The cached target/Keller/Abadi PDFs are reused immutable references from scout retrievals, not re-fetched. New target-page/search and Aldous-body requests have UTC/status/URL/byte/hash bindings in access.json and broader-access.json; new originals and copies were hash-checked before reading. Current page SHA256 9882a1eeefaec26726d2ea7378d80a857a06f31e5f15e84397a2b2bc355347f7. No 403/429/challenge occurred in these three lawful requests. Denied GitHub API/raw/codeload/diff/patch, ScienceDirect and Google challenge routes were not retried. No proxy/TLS-disable/browser bypass; inaccessible historical intervals remain parked. No new current public-registry head, exhaustive historical theorem-body search, complete citation graph, or published-target-body correspondence is claimed. Scout history summaries are provenance, not independent correctness evidence.

Independent check.py uses only exact Fraction arithmetic. Final fresh run passed 16 cases, all 1≤s≤r≤3, single target plus every distinct-pair overlap, n=2r+3. For every original r-set H it compares direct old-complement swap enumeration with the independent lump formula; it checks row sums, nonnegativity, stationary detailed balance, exact one-target q, pair union-flow bound, downward killed-state spectrum, and survival agreement at t=0,...,12. check-results.json contains all cases. This is a diagnostic for transcription/model errors, not proof of perturbation or asymptotics. First run failed on a zero-weight infeasible branch in the checker, repaired by skipping that branch; the failure remains in FAILURES.md. Final checker guard exited 0, peak sampled group RSS 13189120 bytes, wall 0.361s; no cap increase.

finalmanifest.json excludes itself and verification-receipt.json. A separate guarded verify.py invocation after final writes checks every manifest file, before/after original/copy scientific hashes, live retrieval bindings, and fresh PDF-to-text extraction of the three reused primary bodies. The receipt, not this prose, records the actual result. No root acceptance or count action is performed.
