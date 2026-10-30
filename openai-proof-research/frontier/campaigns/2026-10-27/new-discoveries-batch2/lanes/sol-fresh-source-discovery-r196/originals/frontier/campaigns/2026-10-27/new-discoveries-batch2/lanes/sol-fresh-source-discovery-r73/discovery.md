# r73: Sun's quantitative binomial coprimality question — unresolved

## Scope and screening

Solo, assigned-lane-only. Campaign state read: 7 additional / 37 total, next 38; no count or acceptance edits. Ancestor and batch AGENTS, ledger, prior-campaign-context and NEXT read; r57–r71 summaries reconciled, r72 summary consulted solely to avoid overlap. `context-screen.json` records a content search of 414 older summary-named files under openai-proof-research, with hashes and explicit terms. No matching selected-source hit; this is a local duplicate screen, not proof of novelty. In particular r71 semigroups, r67 finite cones, r70 irregulators and r72 Rademacher moments are not pursued.

Three actual source questions screened (other search results were unselected leads):

1. Tărnăuceanu's same-order abelian-group sum-of-element-orders conjecture, as explicitly stated in Amiri, arXiv:2511.08320v2, Conjecture 1.1: for **all finite abelian groups G,H with |G|=|H|**, psi(G)=psi(H) iff G is isomorphic to H. Actual latest-v2 Theorems 1.3/1.4 already assert the full conclusion, via LCM-group order type. Exclude as publicly resolved; no independent audit of that paper's correctness or investment in reproof. v2 dated 2026-05-09, well before this lane. Actual source HTML and live abstract retained.
2. Zeng–Pintér–Fu–Tian, Mathematics14(1),127 (2026), DOI10.3390/math14010127, advertised conjecture: for every m>=1 and fixed m distinct primes, T_n=n(n+1)/2 equals their product with **all exponents positive** for at most m positive n. Primary indexed abstract found, but actual article request returned HTTP429. DEFER, no retry, alternate-host evasion, theorem-body clearance or mathematical investment. Its actual conjecture label and closest theorem bodies remain unverified. This explicitly fails the source-body gate.
3. Selected: Zhi-Wei Sun, OEIS A390107, authored 2025-10-25, internal revision #20 stamped 2025-10-29. For **every integer n>=1**, there is an integer **1<=m<=floor(sqrt(3n+4))** such that

   gcd(m(n-1)+1, binom(m n^2,m n))=1.

This existential formulation includes existence of the sequence's least value. No interpretation based on an empty solution list or an open tag. Actual primary page read by public web tool; direct Python GET403 retained without retry. Page's generic site-footer modification date does not date the conjecture. `sources/sun-web-evidence.md` is a transcribed tool-visible statement, not downloaded raw HTML.

## Actual closest source bodies, read early

He–Yuan, *Results on some conjectures about binomial coefficients*, Bull.Math.Soc.Sci.Math.Roumanie67(2024)429–448, actual publisher PDF, pp431–432: Theorem1.8 settles the first implication of Sun's old Conjecture1.10; Theorem1.9 settles the second implication **assuming k!=l**. The following Remark explicitly leaves: for every k>=3, some t>=1 has ((k-1)t+1) not dividing binom(k^2 t,kt). Their last proof pp446–447 preserves k!=l and uses known Sun theorems for off-diagonal cases. Their Kummer theorem p429 and Lucas Lemma2.1 p432 are the relevant classical tools. PDF bytes, SHA and extracted full text retained.

The 2025 question is stronger: set k=n,t=m, and require coprimality and a quantitative bound. Nondivisibility alone does not give coprimality. Conversely, n>=3 gives d=m(n-1)+1>1, so the selected full claim would imply the old missing existence case. This is a scope relation, not a new counted result. Source2012 original article body has not been separately retrieved; He–Yuan's explicit quotation is the body-read comparison for that older question. No unseen theorem is presumed absent.

## Investigation 1: exact carry criterion

Write d=m(n-1)+1, N=mn^2, K=mn. For a prime p|d,

v_p binom(N,K) = sum over e>=1 of (floor(N/p^e)-floor(K/p^e)-floor((N-K)/p^e)).

Each summand is 0 or 1, and equals 1 iff K mod p^e > N mod p^e. This follows directly by writing N,K in quotient/remainder form; it is also Kummer's carry criterion. Hence the desired coprimality is equivalent to **every** such digit inequality for every p|d and every e with p^e<=N. The criterion is exact and bounded for each input, but does not remove the universal n quantifier.

For q=p^e dividing d, the residues simplify to K mod q=(m-1) mod q and N mod q=n(m-1) mod q. HOWEVER powers beyond v_p(d) must also be checked. Genuine source input n8,m2 has d15, N128,K16; its p3 first-digit inequality passes (1<=2), but q9 fails (7>2). Its sole nonzero p3 floor summand is q9. Checking just prime powers dividing d is invalid. This is a failed helper criterion, not a source counterexample: m4 works.

A further necessary restriction follows from the elementary identity

binom(mn^2,mn)=n binom(mn^2-1,mn-1).

Thus n divides B and any successful m has gcd(n,m-1)=1, since gcd(n,d)=gcd(n,m-1). This explains why many candidate m are excluded simultaneously; it supplies no sufficient condition. m1 fails for n>1; n1,m1 works.

## Investigation 2: exact prime-modulus route and its failure

For n>=2,m>=2 with d prime, success is equivalent to m<=n.

Proof of success: K=d+m-1 and N=n d+n(m-1). For m<=n, 0<=n(m-1)<d and n<d. Their base-d digits are respectively (1,m-1) and (n,n(m-1)), so Lucas gives a nonzero residue. The small coefficients binom(n,1) and binom(n(m-1),m-1) are nonzero modulo d because both upper indices are <d.

Proof of failure: m=n+1 gives d=n^2, which is not prime. If m>=n+2, then n(m-1)=d+m-n-1, with 0<=m-n-1<m-1<d and n(m-1)<2d. The first base-d digit of N is m-n-1 and that of K is m-1, so there is a carry and d divides B. This argument also covers n2 whenever the modulus is prime; no high-digit restriction is needed for the obstruction.

For n>=4, the source bound is <=n. A prime of form m(n-1)+1 for 2<=m<=floor(sqrt(3n+4)) therefore suffices. But n20 has bound8, and the seven moduli are 39,58,77,96,115,134,153, all composite. Yet m2 succeeds (gcd(39,binom(800,40))=1). Thus the short-prime menu fails even on genuine source inputs. Dirichlet's theorem is no bridge: it gives no required short interval, and prime moduli with m>n are actually bad. No claim is made that a new prime-distribution theorem is necessary, since successful composite moduli exist.

## Investigation 3: saturation and exact bounded checks

`run.sh` uses only standard-library integer arithmetic and the unchanged recent guard. 1600 literal big-binomial/gcd evaluations are independently compared with factorial valuations and Lucas digit tests; source terms are reproduced. Exhaustive n1..100000 least-m calculations find no violating input. Maximal observed m is82 at n54974. The maximum m^2/(3n+4) is exactly1 at n32,m10. This is a finite diagnostic, not a universal proof or new credit.

`route-checks.json` gives complete local carry certificates for m1..9 failing at n32, and all prime factors of d311 passing at m10. This verifies a32=10 and shows that holding coefficient3 fixed cannot reduce the additive4. It is only a parameter instance; not nominated. Additional exact tests compare the entire prime-modulus equivalence on n2..150,m2..200. No stochastic floating experiment or numerical-as-proof claim.

## Exact remaining gap and strongest objection

Missing lemma (equivalent in strength to the unproved source endpoint): for every integer n>=2, the set of integers 2<=m<=floor(sqrt(3n+4)) is not covered by the bad-carry sets

{m : exists prime p dividing m(n-1)+1, exists e>=1, (mn mod p^e) > (mn^2 mod p^e)}.

Neither necessary gcd filtering, the short prime menu, nor low-digit constraints proves this noncoverage. A full falsifier is ONE n for which every allowed m has an explicit such p,e certificate. A failure of the prime menu, or a bad individual m, is not such a falsifier. No complete ordinary proof or full-source refutation exists in this lane.

Strongest substantive/classical-bridge objection: all deductions here are standard binomial identities, Lucas/Kummer criteria and finite computations. They earn zero discovery credit even if useful for later work. If the full bound follows from a known short-progression or carry-avoidance theorem, that exact bridge must be body-read and assessed before nomination. No new generic theorem has been claimed. No PROOF.md, Lean or paper is warranted.

## Registry and chronology limitations

Before significant arithmetic work: dated complete named scopes in r57 and the polyomino review were lexically screened, and current public web registry searches run. Full query text and limits are in provenance.json. Actual pinned Omega Problems/coprime-divisor-tuples.md and actual D5/S3/Arith/CoprimeDivisorTuples.lean were fetched/read: they concern Wiseman's A062319 count of pairwise coprime divisor tuples, not A390107 or this binomial. Its source comment dates2021, registry text references revision2026-08-30. Its `.result` proves a divisor-count product via exponent-vector bijections; there is no demonstrated carry-avoidance bridge. No Lean replay performed or required for this non-subsumption scope comparison.

Current dev README fetched successfully, but does not establish a current head or whole-tree coverage. Inherited API403/429 limits respected: zero API calls/retries, no reset evidence, no bypass. Omega6c27b0a… observed15:49UTC remains ONLY latest observed, NOT currentHEAD. r57's D5 tree is Blueprint markdown, distinct from the older actual Lean D5 scope. Actual pinned Lean proof read separately; no inference of absence from failed/incomplete searches. No all-registry or worldwide novelty clearance; freshnessHOLD.
