# Independent review of the NEW renewal bridge

2026-10-30. Solo; no children. Recommendation: **ordinary mathematics PASS; EXCLUDE_ROUTINE_CLASSICAL_ADAPTATION for discovery credit; priority HOLD; formal NOT READY**. This recommendation concerns the substantive new derivation in RENEWAL-BRIDGE.md, not a second audit of the unchanged spectral argument. Root alone decides acceptance/counting. Baseline remains 9 additional /39 total /next40. No shared file, git, public service, MathDB, Lean or manuscript was changed.

The argument proves the expected cover-time asymptotic for every FIXED integer pair 1≤s≤r as n→∞, with uniform deletion from the current r-set and independent uniform addition from its OLD complement:

    E T ~ (r/s) binom(n,s)/binom(r,s) log binom(n,s).

Only 2≤s<r is a prospective new contribution. The source already proves r=s. For s=1, the number k of unseen coupons decreases with probability k/(n−r), giving (n−r)H_(n−r) additional transitions. No growing parameters, distributional limit, alternative update rule or separate boundary credit follows.

## Binding and source scope

freeze.py bound 153 immediate-input/body files before scientific reading, verifying original-before = copy = original-after SHA256. It copies no historical frozen tree. bindings.json identifies every original and copy. The lane reuses previously retrieved immutable PDFs, with no network request. Administrative AGENTS/ledger/context are snapshots; inspect.py fully parsed both administrative JSON files. Ancestor/batch rules were read. Fresh guarded pdftotext extraction exactly matches all five body texts used here (extraction-check.json). Final independent verification checks scientific originals again; administrative originals are intentionally not required to remain unchanged.

Actual published target: Athreya–Mukherjee–Mukherjee, Journal of Theoretical Probability 38 (2025), article54, DOI https://doi.org/10.1007/s10959-025-01417-w, published online 28 May 2025. Literal Conjecture2.4, PDF/printed p6, specifies the OLD-complement walk and the formula above. Theorem2.5 p7 and proof pp17–19 prove r=s. Remark2.2 p7 gives slowdown r/s. Actual source proof bodies used here also include Lemma3.2/Corollary3.3 and the missing-count proof of Theorem2.1, pp10–13. Those bodies already provide logarithmic-time comparison, missing-count second moment and summed expectation tails in the iid model.

Actual correction, DOI https://doi.org/10.1007/s10959-025-01432-x, article77, published 15 September 2025, all three pages inspected. The dependent formulas retain n and r/s; no resolution/withdrawal of Conjecture2.4 is present. Preserve the correction's p2 introductory **iid** anomaly: its replacement numerator literally uses binom(r,s) log binom(r,s), while the same line's right expression grows as n^s log n. This is inconsistent for fixed r,s. It neither changes the literal dependent target nor licenses silently repairing the document. The 2023 preprint (v1 3 April; v2 12 September) predates journal/correction; the present renewal derivation is dated 30 October 2026. No current priority certification is made.

## Adversarial verification, step by step

Write N=binom(n,s), p=binom(r,s)/N, q=sp/r. For a single target or distinct pair put W=S or S∪U, m≤2s, B=H∩W, o=∅; A consists of states containing either target and D is its complement. For n≥m+r the feasible states are all B⊆W with |B|≤r. The transition rule in the bound original proof is the correct projection: distinguished deletion probability 1/r per member, outside deletion (r−|B|)/r, distinguished addition 1/(n−r) per OLD missing member, outside addition (n−m−r+|B|)/(n−r). In particular a deleted distinguished member cannot be immediately re-added. This is the only unchanged finite-chain interface reused.

**1. Uniform returns, including self-loops.** At each nonempty state select deletion of some distinguished member (probability ≥1/r), and select an outside-W addition (probability ≥1−m/(n−r)). Repeat until empty, at most r steps. Thereafter keep additions outside W to pad to r steps; at o deletion is necessarily outside W. Thus, for all sufficiently large n, P_x(τ_o≤r)≥c=(1/(2r))^r uniformly in x (a smaller fixed c is harmless). Markov iteration yields P_x(τ_o>kr)≤(1−c)^k. From o, apply this bound after the first transition to the POSITIVE return L; L=1 is permitted and overwhelmingly likely. Hence sup_n E exp(aL)<∞ for some a>0. No irreducibility/mixing estimate of the growing full chain is used here.

**2. Occupation and mean return.** Let g(x)=E_o Σ_(j=0)^(L−1) 1_(B_j=x). Finite E L and nonnegative summation justify gP=g: the time ranges 1,...,L and 0,...,L−1 differ only by equal endpoint states o. The projected finite chain is irreducible for large n (reachable projections of the connected swap graph), so g/μ=π, μ=E L. Exactly one of these occupation times is o, hence g(o)=1 and μ=1/π(o). With π(B)=binom(n−m,r−|B|)/binom(n,r), π(o)=1−O(1/n) and μ=1+O(1/n). Counting transitions j→j+1 with j<L gives E V=Σ_D g(x)P(x,A)=μQ, where V counts D→A entries. The terminal transition to o contributes zero; no boundary entry is omitted.

**3. Repeat entries and relative calibration.** Every path from D to A before o must have a distinguished addition; D may contain incomplete targets but cannot enter A by deletion alone. For τ_o started at x∈D, stopped-step conditional addition probabilities are ≤m/(n−r). The union bound plus E_x τ_o≤C gives P_x(τ_A<τ_o)≤η=C'/n, uniformly. At x=o, τ_o=0 and this inequality is interpreted literally; positive-return cycle success is handled separately. After each entry into A there is an exit into D before the return to o. These stopping times are finite by the same return tail. Strong Markov at those exits implies

    P(V≥j+1 | V≥j) ≤ η, j≥1;
    h=P(V≥1) ≤ E V ≤ h/(1−η).

Consequently (1−η)μQ≤h≤μQ, so h/μ=Q(1+O(1/n)) RELATIVELY. This does not follow from an absolute O(1/n) approximation, which would swamp q=Θ(n^(−s)). The potentially nontrivial local clustering within A is already accounted for by counting entries rather than occupation times. No additional extremal-index theorem is assumed.

**4. Exact one/pair flux, independently rechecked.** Uniform r-sets are reversible because every swap and its reverse have probability 1/[r(n−r)]. A single target has mass p and exit probability s/r, exactly, so Q_1=q. For a distinct pair put I=A_S∩A_U, X=A_S\A_U, Y=A_U\A_S. The difference between the sum of separate exit flows and the union exit flow is exactly

    Q(X,Y)+Q(Y,X)+Q(I,D)+Q(I,X)+Q(I,Y).

Here D is outside the union. The intersection mass is zero if |W|>r and otherwise O(p/n), since |W|≥s+1. Each X→Y transition needs a distinguished U addition, probability ≤s/(n−r); reverse likewise. Thus 0≤2q−Q_2≤2ps/(n−r)+π(I)=O(p/n), and Q_2=2q(1+O(1/n)). This check is independent of spectral perturbation. Only s overlap types occur, so constants are uniform over all distinct pairs.

**5. Un-killed iid cycles and concentration.** Strong Markov at successive positive returns gives iid whole cycles, hence iid pairs (L_i,success_i). Killing at success would destroy this construction and is not done. Uniform exponential moments and bounded μ give, by the centered Taylor remainder, E exp(u(L−μ))≤exp(Cu²) for |u|≤u0, uniformly in n. Since L≥1, C_t=max{k:R_k≤t} is finite. Put k_−=floor((1−δ)t/μ), k_+=ceil((1+δ)t/μ), 0<δ<δ0. Events C_t<k_− and C_t>k_+ imply respectively R_k−>t and R_(k_++1)≤t. Their mean gaps are at least δt (the extra +1 only helps the latter); Chernoff with |u| proportional to δ gives Cexp(−cδ²t) when δt is large. For small δt enlarge C so that the bound is ≥1. This covers t=0, k_−=0, floors and ceilings without an unstated large-time restriction.

**6. Survival inclusions, no false independence.** If C_t≥k_− and survival holds, the first k_− full cycles all failed. If the first k_++1 cycles fail and C_t≤k_+, survival holds even during the current partial cycle. Taking probabilities and subtracting only the cycle-count error gives exactly

    (1−h)^(k_++1)−Ce^(−cδ²t) ≤ S_o(t)
        ≤ (1−h)^k_−+Ce^(−cδ²t).

Only independence of different complete cycles is used to evaluate deterministic-index failure probabilities. Lengths and marks within a cycle can be arbitrarily dependent.

**7. Relative growing-time tails and stationary start.** Take δ=n^(−1/4) and t=floor(θ log N/q), fixed θ>0. Errors in the geometric exponent are O(δlog N+log N/n+qlog N)=o(1). The Chernoff exponent δ²t=Θ(n^(s−1/2)log n) dominates every fixed multiple of log N; thus its additive error is negligible even compared with N^(−2θ). It follows that S_o(t)=exp(−Qt)(1+o(1)). For stationary start let R=inf{j≥0:B_j=o}, J=floor(δt). Strong Markov and monotonicity give

    π(o)S_o(t) ≤ S_π(t) ≤ S_o(t−J)+P_π(R>J).

The upper bound discards initial hits, so is valid without controlling initial conditional survival. P(R>J)≤Ce^(−cJ), QJ=o(1), π(o)→1. This is the needed multiplicative squeeze; no additive π(A)=O(p) error is subtracted from a pair probability of order N^(−2θ). The uniform one/pair stationary tails are N^(−θ)(1+o(1)) and N^(−2θ)(1+o(1)).

**8. All-time bound and full expectation.** For every integer t≥0 the preceding upper bound and the return-delay inequality give

    S_π(t) ≤ Cexp(−Q(1−Cδ)t)+Cexp(−cδ²t).

Use h/μ≥Q(1−C/n), k_−≥(1−δ)t/μ−1 and J≤δt; powers lost to floors cost a bounded factor, and exp(−cδt)≤exp(−cδ²t). Since δ≥1/n this yields the stated exponent uniformly. For one target choose α=q(1−Cδ)>0 and t0=ceil((log N+sqrt(log N))/α). Summing the union bound after t0 costs O(e^(−sqrt(log N))/α)+O(Nδ^(−2)e^(−cδ²t0)), both o(q^(−1)log N). Before t0 use probability ≤1. For the lower bound, θ=1−ε gives E M=N^ε(1+o(1)), E[M(M−1)]/(E M)^2→1, and Var(M)/(E M)^2→0. Thus P(T>t)→1 and E T≥tP(T>t); let ε↓0. Permutation transitivity of the COVER statistic makes stationary and any deterministic initial r-set equivalent; it does not assert that fixed-target hitting laws are initial-state invariant. Round indexing changes the endpoint by at most one. This closes the expectation, rather than only a high-probability endpoint.

No scientific repair of RENEWAL-BRIDGE.md is needed. The expansions above remove possible ambiguity in its compressed steps.

## Generic counterexamples and exact safeguards

1. Cycle length/mark independence is false even in a two-state example: P(o,a)=ε, P(o,o)=1−ε, P(a,o)=1. A successful cycle has length2 and an unsuccessful cycle length1. Its mgf is (1−ε)e^u+εe^(2u); h=ε, μ=1+ε, Q=ε/(1+ε). The reviewed inclusions work; conditioning on C_t and inserting independent geometric failure probabilities need not work.
2. π(o)→1 by itself does not imply a uniform return mgf or h~μQ. In the same two-state family replace P(a,o) by ε² and P(o,a) by ε³. Then π(o)=1/(1+ε)→1 while E_a τ_o=ε^(−2), and no uniform exponential moment exists. Repair: retain the explicit r-step minorization, not just the stationary mass.
3. Repeated entries cannot generically be discarded. In a chain with transitions o→a at probability ε, a→b deterministically, b→a at probability1/2 and b→o at probability1/2, let A={a}. A successful cycle has an expected two entries, so E V=2h, not h(1+o(1)). Repair: the stopped distinguished-addition estimate η=C/n at every D exit. This is a specific necessary model check, established in step3.
4. An absolute error O(q) in exponential approximation does not justify relative pair tails near θ=1: q=Θ(N^(−1)), while N^(−2θ) is smaller for θ>1/2. Nor does h/μ=Q+O(1/n) calibrate order-n^(−s) rates. Repairs are steps3,6,7 and the multiplicative stationary squeeze.
5. Collapsing A into a vertex need not preserve the original entrance path law. If a,b∈A have escape probabilities1 and1/2 to o, the future escape law depends on which entrance occurred. A stationary-weight collapsed chain cannot silently replace this path process. The actual distinguished-union projection is Markov by explicit transition counts; no arbitrary target collapse is used.

## Closest bodies and substantive judgment

Body coverage is itemized in body-coverage.json. No abstract, open label, missing keyword or proof length is used as novelty evidence.

* The actual source iid proof supplies the final first/second-moment and expectation-summation architecture. Its r=s proof supplies distinguished-overlap reduction and symmetry, but vertex Matthews alone would not cover overlapping target sets for s<r. The new route supplies the missing relative single/pair tail interface before reusing those elementary source steps.
* Aldous–Fill, official author-hosted book https://www.stat.berkeley.edu/~aldous/RWG/book.pdf, §3.5.4 printed pp85–87, Propositions3.22–3.23 and the proof reducing the spectral second moment: stationary continuous-time subset-hitting absolute error ≤τ2/EπT_A. This alone is insufficient at polynomially small pair tails and does not calibrate the union hitting mean. No direct theorem application is asserted.
* Cooper–Frieze–Pegden, https://arxiv.org/pdf/1810.04772v2, §2 Lemma4, return generating functions and AppendixA proof: this DOES provide relative first-visit exponential tails plus an exponentially small remainder, with rate π_v/[R_v(1+O(ω^(−1)))]. Its hypotheses include mixing and nonvanishing of the truncated return polynomial. Neither the target sets nor their entrance laws become a legal singleton application automatically. Direct application requires an actual return-kernel/normalizer verification; the reviewed route avoids that theorem by proving the necessary elementary renewal bounds. The source theorem is not being dismissed as only a weak exponential limit.
* Keller, https://arxiv.org/pdf/1202.3900v1, §2 assumptions(1)–(6), §3.1 equations(15)–(22), §3.2 Proposition2 and proof, pp2–8: quantitative spectral hitting tails and correlation-adjusted escape rates already exist. Direct REPFO application is not furnished for this n-dependent finite-chain family; an unspecified limiting extremal index alone lacks the o(1/log N) precision. The new renewal proof removes all operator hypotheses rather than claiming Keller directly settles this instance.

**Full applicable bridge for the exclusion recommendation:** the generic regeneration calculation in steps1–3,5–8 says that a family with an atom o, uniform return exponential moments, π(o)→1, repeat-entry probability η=O(1/n), single flux q=Θ(n^(−s)), pair flux 2q(1+O(1/n)), and N=Θ(n^s) has the claimed cover mean. Every hypothesis has been proved above for this model: downward deletion gives the atom bound; stopped rare additions give η; reversibility plus one elementary union-flow expansion gives pair calibration; the source's missing-count method then gives the cover endpoint. There is no residual mixing, return-polynomial, perturbation or concentration hypothesis waiting to be checked. In particular the difficult-looking normalizer is obtained from exact occupation stationarity and the one-line geometric repeat-entry estimate, not from a new analytic inequality or unresolved model theorem.

This reverses provisional substantive retention **for the new route**: under the campaign's prohibition on routine classical adaptations, I recommend exclusion. It is an independent judgment of the complete applicable bridge, not an assertion that one of the cited theorems literally states this final conjecture. The bridge contains model-specific work, especially the repeat-entry and pair-normalizer checks; those are real and necessary, but are exhausted here by bounded-step deletion, an addition union bound, and stationary edge counting. Their presence does not by itself justify substantive credit. No earlier published exact full-scope proof has been established by this review. Priority remains HOLD independently, and root may adjudicate this recommendation against the campaign standard.

## Finite formal dependency plan, without builds

No Lean readiness claim. A finite dependency graph would be:

1. `ProjectedSwapKernel`: exact projection, stationary weight and detailed balance, finite feasible state space, cover relabeling invariance.
2. `ReturnBlockBound`: P_x(τ_o>kr)≤(1−c)^k and a uniform exponential moment for positive return, explicitly allowing self-loops.
3. `CycleOccupation`: gP=g, g=μπ, g(o)=1, and E V=μQ for stopped transition counts.
4. `StoppedRareAddition`: addition hazard ≤m/(n−r) implies the pre-return hit bound; strong Markov gives E V≤h/(1−η).
5. `MarkedRegeneration`: iid un-killed path cycles as pairs; deterministic-index failure probabilities and the two survival inclusions, with no length/mark independence assumption.
6. `RenewalChernoff`: centered uniform mgf to cycle-count bound for all integer t, floor/ceiling conventions included; then stationary-start multiplicative squeeze.
7. `OnePairFlux`: exact q and uniform pair 2q(1+O(1/n)), all overlap types, impossible intersections included.
8. `LogTimeAndTailSum`: relative single/pair asymptotics, missing-count second moment and full expectation-tail summation, then the literal source endpoint including indexing.

This removes complex contours, Riesz projections and uniform matrix-power remainders and therefore materially reduces the required analytic machinery. It does not remove stopped-path measure theory, strong Markov/iid excursion construction, uniform mgf/Chernoff estimates, or quantitative asymptotic/tail-sum infrastructure. No library audit/build was performed; reduced machinery does not establish low effort or a completion estimate. Given the exclusion recommendation, further formal investment is not recommended for discovery credit.

## Access, provenance and limitations

No new retrieval was necessary to decide this derivation review. Inherited registry denials, old inaccessible historical intervals and IEEE empty challenge response are parked; none were retried. No GitHub API/raw/codeload/diff/patch, ScienceDirect, Google challenge, browser, proxy or TLS-disable route was used. Current public proof-registry clearance, complete citation graph and worldwide priority remain unavailable. Exact inherited URLs/statuses/timestamps are retained in bound access/provenance files; provenance.json maps the five bodies to those references and hashes. This review does not convert earlier metadata-only screens into body coverage.

No finite sweep substitutes for proof. The independent counterexamples in objections.md are exact, hand-checkable controls. FAILURES.md preserves the overly broad initial filename listing and output truncations; none affected the freeze-before-reading boundary. finalmanifest.json excludes itself and verification-receipt.json. verify.py is run separately under the prescribed guard after final writes, checks every manifest member and scientific original/copy hash, and records actual results in the receipt.
