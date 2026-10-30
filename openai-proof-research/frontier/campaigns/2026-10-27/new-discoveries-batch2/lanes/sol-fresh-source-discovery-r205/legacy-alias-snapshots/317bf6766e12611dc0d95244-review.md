# Independent adversarial review: factorial-product collision

Reviewed candidate: `sol-fresh-source-discovery-r115`. Solo review; no children, git, browser, messages, accounts, posting, uploads, Lean, manuscript, or shared writes. All review outputs are in this lane. Root check/adoption were read as context, not inherited as proof. Counts remain 8 additional / 38 total; this review awards zero credit.

## Verdicts

| Gate | Verdict |
|---|---|
| SOURCE | PASS: actual published question, intended domain and full Theorem 4.6 proof checked |
| MATH | PASS: complete finite refutation; independent exact checker PASS |
| SUBSTANTIVE | ELIGIBLE with a serious classical-counting objection; genuine boundary beyond the source theorem, not a routine source adaptation; root adjudication remains authoritative |
| NOVELTY | BOUNDED / NOT CLEARED globally: no earlier same-object resolution located; no claim that the bridge below was previously published |
| FORMAL feasibility | HIGH for the finite witness, untested; no formal artifact produced |

The substantive recommendation is deliberately separate from historical novelty. I did not find a published earlier collision or an actual prior theorem directly supplying this distinct-support collision. I did find a complete classical counting route, supplied below, which considerably strengthens the contrary case beyond a generic integer kernel. On balance I judge this a genuine boundary result eligible for further gates: the source's distinct-prime proof does not adapt, and the alternate argument requires a problem-specific smooth restriction and concentration step. Deriving another complete solution from classical ingredients is not by itself evidence of a routine published corollary. This is bounded eligibility, not acceptance or a global priority claim.

## Exact statement and source scope

Aivazidis–Loukaki–Müller, *On the common transversal probability*, J. Group Theory 27 (2024), 1233–1285, DOI `10.1515/jgth-2024-0030`, published Problem 5.6, p.1281 (preprint Problem 12.6). The statement asks whether equality

    ∏_{i=1}^n f(t_i) = ∏_{j=1}^k f(s_j),   f(x)=Γ(x+1)/x^x,

for distinct integers greater than one implies n=k and equality of the lists after rearrangement. There is no sum constraint, equal-length assumption, prime-factor restriction, or requirement that these lists arise from a group. On either interpretation of distinctness (within each list, or across the two lists), the disjoint witness qualifies. The independently viewed cached rendering p1281.png confirms the formula and adjacent question boundaries; published PDF and extracted text were read. No abstract or MathDB label substitutes for this read.

Actual Theorem 4.6, pp.1263–1265, assumes that one entire side consists of distinct primes; the other side allows positive integers >1 with repetitions. I read its whole induction, largest-prime cancellation, Bertrand-prime valuation argument, and final majorization step. Its k=1 case uses monotonicity of t!/t^t. In the induction, a prime q larger than every right-side prime forces many large left-side entries, leading to the majorization contradiction. Both proposed supports contain composites, so neither orientation satisfies that theorem. In particular, the positive valuations at primes 11 and above can be shared by both sides; the proof's zero valuation on the prime side cannot be transplanted. Theorem 4.6 does not refute or produce this witness.

I also read the actual Aivazidis–Loukaki–Sambale author manuscript dated July 27, 2023: Theorems A/B, Lemma 3.1 and full Theorem A proof (primary reduction, induction on rank, then elementary-abelian hyperplane avoidance). These concern common complements/transversals of specified subgroups of finite abelian groups. They do not assert factorial-product injectivity or a same-object collision. The cached manuscript's date is preserved; calling it a successor does not imply publication after the 2024 article.

Problem 5.2's subgroup inequality and Problem 5.8's minimizer question receive no nomination or credit here.

## Independent arithmetic proof

Set A={3,5,6,7,8,14,16,20,36} and B={4,10,12,15,18,21,32}. All sixteen entries are different integers >1, and the cardinalities are 9 and 7. For a prime p, counting multiples of p^j in t! gives

    v_p(t!/t^t)=Σ_{j≥1} floor(t/p^j) − t v_p(t).

The independently recomputed totals are:

| p | A | B |
|---|---:|---:|
| 2 | -123 | -123 |
| 3 | -37 | -37 |
| 5 | -4 | -4 |
| 7 | -8 | -8 |
| 11 | 6 | 6 |
| 13 | 5 | 5 |
| 17 | 3 | 3 |
| 19 | 2 | 2 |
| 23 | 1 | 1 |
| 29 | 1 | 1 |
| 31 | 1 | 1 |

Every higher prime has valuation zero because each t≤36. Unique factorization of positive rationals therefore gives both products as

    11^6·13^5·17^3·19^2·23·29·31 / (2^123·3^37·5^4·7^8).

The identity Γ(t+1)=t! identifies this with the literal source expression. The unequal lengths contradict its asserted conclusion. This is a full ordinary refutation, not numerical evidence. No minimality, group realization, or replacement theorem is necessary.

`exact_checker.py` was independently written without importing candidate code. It checks distinctness, disjointness, 176 individual valuation entries by two formulas, all eleven column totals, exact Fraction multiplication, and the 240-digit integer cross product. `exact-receipt.json` records PASS and the exact integers; `exact-guard.log` records successful capped execution. Run from the workspace root:

    python openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-factorial-product-preliminary-review-r1/exact_checker.py

## Complete classical distinct-support bridge

Here is the strongest contrary case, derived in this review rather than attributed to an unlocated prior paper. It proves existence of a counterexample with distinct supports directly. It does not need or explain the particular maximum-36 witness, and it does not assert unequal cardinalities; neither is required to refute the full injectivity conclusion.

Use natural logarithms. The sole external estimate needed is

    π(x) < C x/log x  (x>1),  C=1.25506.

This is Rosser–Schoenfeld, *Approximate formulas for some functions of prime numbers* (1962), §3, Corollary 1, equation (3.6), actual primary PDF body retained and read. No prime number theorem or smooth-number asymptotic is assumed. The concentration inequality used next is proved here.

Let N→∞, L=log N, y=N/L², and let T be the integers t in [2,N] all of whose prime factors are ≤y. If an integer is excluded, it is divisible by a prime p>y. Partial summation and the displayed prime bound imply

    Σ_{y<p≤N} 1/p
      = π(N)/N − π(y)/y + ∫_y^N π(u)/u² du
      ≤ C/L + C log(log N/log y)
      = O(log L/L) = o(1).

The union bound on multiples of these primes gives N−1−|T|≤N Σ_{y<p≤N}1/p=o(N). Thus m=|T|=N−o(N).

For each subset U⊆T and prime p≤N put V_p(U)=Σ_{t∈U} v_p(f(t)). Choose U uniformly, so its membership bits X_t are independent fair Bernoulli variables. For large N, y>√N. For p>y and t∈T, p∤t and p²>N; consequently

    v_p(f(t)) = floor(t/p),    0≤v_p(f(t))≤L².

Write a_t=floor(t/p), μ_p=Σ a_t/2, and S_p=Σ a_t²≤NL⁴. Since cosh z≤exp(z²/2) (compare the power series, using (2k)!≥2^k k!), independence yields

    E exp(λ Σ a_t(X_t−1/2)) ≤ exp(λ² S_p/8).

Markov's inequality, optimized at λ=4u/S_p, gives each one-sided tail at most exp(−2u²/S_p). The S_p=0 case is constant and harmless. Take

    u=L² sqrt(N log(4N)).

Then Pr(|V_p−μ_p|>u)≤2/(4N)²=1/(8N²). Union over fewer than N primes shows that more than half of all 2^m subsets simultaneously satisfy |V_p−μ_p|≤u for every p>y. Each such coordinate has at most 2u+2 integer values. Hence their combined number of possible large-prime coordinate vectors is at most

    (2u+2)^{π(N)},

whose natural logarithm is at most

    (C N/L)·(L/2 + O(log L)) = (C/2+o(1))N.

For p≤y, each |v_p(f(t))|≤N(1+log_2 N): the factorial valuation is at most N and t v_p(t)≤N log_2 N. Thus each subset sum lies in an interval with at most 2N²(1+log_2 N)+1 integer values. There are at most y such primes, so these small-prime coordinates contribute log-count at most

    y·log(2N²(1+log_2 N)+1)=O(N/L)=o(N).

All primes>N have zero valuation. The good subsets therefore have at most exp((C/2+o(1))N) possible full valuation vectors, whereas there are at least 2^{m−1}=exp((log 2−o(1))N) good subsets. Since C/2=0.62753<log 2, for sufficiently large N two different good subsets U,W share their entire valuation vector. Their positive rational products are equal by unique factorization. Cancel U∩W to obtain disjoint distinct supports A',B'. Neither can be empty: f(t)∈(0,1) for every t>1, so a nonempty product cannot equal the empty product 1. These sets refute exactly Problem 5.6.

This is an actual {−1,0,1} collision argument. Bare dimension counting only supplies an integer kernel with uncontrolled coefficients; it would not suffice. Crude box counting without concentration also fails to give the necessary exponent. Both missing bridges are explicitly supplied above.

Adjudication: the source's prime-side result has a genuine domain boundary, and a finite collision can have substantive value. Neither finiteness nor LLL is an automatic exclusion. The strongest objection is now a complete classical two-scale counting solution of the exact negative question, not merely a vague assertion that factorials have many dependencies. It lowers the claim of technical depth and might lead root to exclude the outcome as a routine application of concentration/pigeonhole. Against exclusion, the smooth restriction and concentration box supply precisely the distinctness bridge missing from ordinary dependence; neither is a specialization of Theorem 4.6, and no inspected prior primary theorem supplies the assembled argument. My judgment is therefore ELIGIBLE, bounded, as a genuine refutation across the source boundary. The alternate argument is fresh review reasoning, not located public prior art and not a separately nominated outcome. If root classifies this complete bridge as routine under campaign policy, it has the full mathematical bridge needed for that exclusion; the reason would be routine derivability, not historical duplication. No counts change here.

## Bounded prior-art and chronology assessment

The candidate's old 403 and capped-compare objections are structurally superseded. I read the gap-closure metadata, including exactcoverage.json, intervals.json, net-changed-paths.json, baseline.json and HTTP receipts, without treating the Rényi semantic disposition as relevant clearance. Eleven uncapped intervals contain 205 commits, covering 1b999d9fda71df7537b62327147496d64a6f66ef through 0a10157da355f1825f38212dd4c2869925ae6785. Seventy formerly missing patch bodies were fetched in that work; 279 actual cached bodies are available. Existing complete baseline trees contain 350197 Omega and 174524 OpenAI entries. OpenAI head is 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a. Actual inherited HEAD/compare HTTP200 receipts are dated 20:58–20:59 UTC on 2026-10-29. No new HEAD request was made; no later freshness is claimed.

This review screened all 279 cached bodies with target-specific patterns, and the three JSON comparison files physically in the closure's comparisons directory. It did not independently reconstruct all eleven patch sets. Complete baseline tree metadata were streamed for factorial, transversal, subset-product, multiplicative-independence and pigeonhole leads; 269 path leads were recorded. Seventeen selected actual registry bodies were freshly fetched at pinned baseline revisions: factorial-ratio parity/integrality families, factorial recurrence, and the OpenAI prime-subset-product module. Actual statements distinguish their objects from f(t)=t!/t^t: the prime module proves injectivity of products of primes themselves; factorial-ratio families concern integrality/parity of indexed ratios. No arbitrary filename absence is promoted to global absence.

The potentially closer Bober factorial-ratio lead was followed to the actual 2007 v1 primary PDF (published 2009): Theorem 1.2 requires balanced parameter sums and height one and classifies ratios integral for every scale n; Theorem 3.1 / Lemma 3.2 concern nonnegative floor defects. I read those bodies and the valuation proof beginning Lemma 3.3. They do not directly assert an equality of distinct subsets of normalized values t!/t^t. No classification/subsumption conclusion is drawn merely from the registry's Bober summary. Rosser–Schoenfeld supplies only the prime count bound in the reviewer-derived bridge, not a previously published answer to Problem 5.6.

A separate bounded stream of original/copy mathematical text across dates read 2993 files / 127992162 bytes and stopped at the declared 128MB cap. Lane/audit/corpus/input/receipt containers were excluded; copied manuscript mathematical text was allowed. Incidental review/progress prose is not used as theorem evidence. The 60 bounded excerpts are mainly unrelated subset products, factorial cumulants and geometric factoriality; no same-object result was found. This scan is incomplete and not a whole-workspace clearance. Receipt metadata and exclusions are in body-screen.json. Candidate audit-manifest/audit-matches, SQLite corpus, and generated hit archives were hashed only, never read as mathematical evidence.

Bounded live web searches (titles, Problem 5.6, factorial multiplicative independence, subset-product/pigeonhole) returned the primary source and unrelated leads; no located prior resolution. Search indexing, author pages and catalogue summaries are not absence evidence. Exact queries and times/limits appear in provenance.json. Candidate creation/retention is preserved as actual 20:xx/21:xx chronology, not backdated: published PDF retained 20:58:27Z; abstract/successor request starts 21:04:38Z; candidate provenance 21:08:55Z. Earlier discovery activity in the 20:xx period is not replaced by these later source receipts. Preprint dates remain 2022-09-02 and 2023-05-31; publication remains 2024. Search engine relative age labels are not publication dates. Any later public match needs content and time adjudication; it is not automatically prior art.

Limits: no MathSciNet/zbMATH sweep, no complete global proof-body sweep, no full semantic read of both baseline registries, no exhaustive factorial-ratio literature, no priority guarantee. No new 403/429/challenge was encountered; no bypass or retry was used. There is an inspection failure preserved here: a shell `head -5` on a minified comparison JSON accidentally emitted a massive single line; tool output truncated it. That output is not treated as a semantic read or novelty clearance. The substantive assessment rests on the explicit bridge and source comparison, not on this failed inspection or unlocated historical results.

## Formal feasibility and falsifiers

The finite proof should be straightforward to formalize with kernel-checked natural/rational arithmetic: define the two finite lists, prove nodup/disjointness and lengths, prove the factorial cross-product equality by explicit arithmetic, establish denominator nonzero, then use the library Gamma-at-natural identity to reach the literal real-valued source statement. A refutation endpoint must quantify over arbitrary distinct lists and negate the exact conjunction of equal lengths/permutation conclusion, not merely state the rational certificate. Estimated effort: small, perhaps 1–3 focused work sessions and 2–5 modules depending on the Gamma API; these are estimates, not tested library facts. No Lean run or paper is authorized or performed. The asymptotic classical bridge is unnecessary for the finite formal endpoint and would cost materially more to formalize.

Strongest mathematical falsifiers: a different source formula, added scope hypothesis, repetition, a differing prime exponent, or failure to bridge Γ(t+1)=t!. All are addressed by actual source reads and the exact certificate. Strongest substantive objection to my eligibility recommendation: root classifies the fully supplied smooth-restriction/concentration application as routine under campaign policy. An error in that counting argument would weaken the contrary case, while leaving the independently checked finite witness intact. Strongest novelty falsifier: an actual earlier same-object collision or a theorem directly guaranteeing this distinct-support collision; only primary bodies and chronology can settle that. Neither a generic integer dependence nor failure to find the exact sixteen entries is dispositive.

## Integrity and handoff

All 44 candidate paths in review-freeze.json (43 payload entries plus manifest) were checked before and after; the freeze descriptor itself was also hashed, giving 45 observed files. All expected hashes matched before and remained byte-identical after. The ~94MB audit manifest and ~122MB SQLite file were streamed only for hashes. See freeze-before.json and freeze-after.json. final-manifest.json hashes this lane's completed artifacts, excluding itself to avoid self-reference. No root-owned adoption, acceptance or counts were edited.
