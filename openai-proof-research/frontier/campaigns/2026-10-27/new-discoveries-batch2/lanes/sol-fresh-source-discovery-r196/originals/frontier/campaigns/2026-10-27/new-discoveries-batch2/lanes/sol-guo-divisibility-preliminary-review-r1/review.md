# Independent preliminary review: Guo divisibility

Recommendation: **EXCLUDE from substantive campaign credit**, for root adjudication. **SOURCE PASS; MATH PASS (ordinary universal proof); SUBSTANTIVE FAIL by complete routine adaptation; NOVELTY HOLD; FORMAL FEASIBILITY plausible, unverified.** This is not a claim that an earlier publication proves the exact conjecture. The all-degree modulus-n² endpoint is stronger than the theorems located in the inspected bodies. The exclusion recommendation is a campaign eligibility judgment about the complete adaptation below, not an inference from proof length or from the conjecture label.

This review is standalone and solo. No children, git, shared edits, external messages/posts/uploads, MathDB edits, browser, Lean, or manuscript work. Root alone decides acceptance and counts. Administrative snapshot: 9 additional / 39 total, next 40; this review assigns no credit. Review UTC and exact retrieval events are in retrieval.jsonl and checker-evidence.json (2026-10-30 UTC; the environment's displayed local date is not substituted for measured UTC).

## SOURCE: exact full published question

I read the actual complete five-page published body, Guo, *On a conjecture related to integer-valued polynomials*, Bull. Math. Soc. Sci. Math. Roumanie 66(114), no.4 (2023), 449–453. Published Conjecture 2, equation (4.1), p452, asks, for every positive integer l,n and every integer 0≤k<n,

    n² | (2l−1)!! Σ[m=k..n−1] (2m+1)^(2l−1) C(m+k,2k) C(2k,k)².

There is no prime, parity, bounded-degree, asymptotic, or extra n>l hypothesis. The sum starts at k. This is the stronger binomial-coefficient question, not only Sun's integer-valued-polynomial consequence, nor Guo's already proved modulus-n Theorem 1. The source explicitly identifies l=1 as proved by Theorem 2. Its subsequent q-analogue is only l=1 and is not the target here.

I also read the complete arXiv source body and the complete Chen–Guo six-page preprint, including Section 4 and the preceding summation/linearization proofs. Independent live downloads of all three PDFs are byte-identical to the frozen candidate copies. Thus the actual-body comparison does not rely on search snippets or abstracts.

Primary versions and exact body SHA256:

* Published Guo: https://bulletin.ssmr.ro/pdf/66-4/articol_8.pdf ; 82b6c27e9dfa800b204a0c707a6c13f43a9880be3e81185a55f6a82deba6267d. Received 8 April 2022, accepted 12 May 2022, journal year 2023. Exact online publication date and DOI not authenticated.
* Guo preprint v1: https://arxiv.org/pdf/2003.12653v1 ; 843fc89a59332b5610a5b33e5ad1d823eac9920e43c2af76541c14e50af2ae68. Current https://arxiv.org/abs/2003.12653 lists only v1, 23 March 2020 10:55:17 UTC. Conjecture 4.1 there is the same equation and full quantifiers as published Conjecture 2; the concluding q-language and bibliography were updated, without resolving this question.
* Chen–Guo: https://arxiv.org/pdf/1412.5734v1 ; 3eba5dbcbc3bb854c867d27ff351747416b783b5bf2382502364e5e0685c0ea5. Current https://arxiv.org/abs/1412.5734 lists only v1, 18 December 2014 07:07:22 UTC. Published citation in Guo is IJNT 14 (2018), 365–370. That later typeset body was not read; no claim about changes between its preprint and publication.

The actual Chen–Guo Section 4 gives an integral shifted-binomial/rising-factorial expansion, its equation (4.1), and uses (2m+1)²=4m(m+1)+1 in (4.2) to reach all odd powers modulo n. The symbol (2j+1)_(2i) there is a rising factorial, not the ordinary power (2j+1)^(2i). Neither its stated congruence nor Guo's Theorem 1 supplies modulus n² by itself. Guo's Lemma 3 gives the exact telescoper needed here. It references Chen–Guo equation (2.4), whereas the corresponding displayed summation in the inspected v1 is (2.5); use the actual identity, not that cross-reference number.

## MATH: independent universal reconstruction

All binomials below have nonnegative upper entries and are zero when the lower entry is too large. Empty products are 1. Write C(a,b) for binomial(a,b). The argument below uses a different coordinate from the candidate recurrence and derives its divisibility structure explicitly.

Fix k≥0. In the polynomial ring Z[X], put

    u_i=(k+i)(k+i+1),
    B_t(X)=Π[i=0..t−1](X−u_i).

For every r≥0 there are integers c_(r,t), zero outside 0≤t≤r, such that

    (4X+1)^r = Σ[t=0..r] c_(r,t) B_t(X),
    4^t | c_(r,t).                                      (1)

Proof: c_(0,0)=1, and XB_t=B_(t+1)+u_t B_t gives

    c_(r+1,t)=(4u_t+1)c_(r,t)+4c_(r,t−1).

Induction proves both the identity and the divisibility; out-of-range coefficients are zero. This is a monic Newton/factorial basis, with no rational interpolation assumptions. Let c_(r,t)=4^t a_(r,t), a_(r,t)∈Z.

For integers m≥k, set X=m(m+1) and q=k+t. Factor each difference as

    X−u_i=(m−k−i)(m+k+i+1).

Consequently

    B_t(m(m+1)) C(m+k,2k)
       = (2q)!/(2k)! C(m+q,2q).                         (2)

If k≤m<q, the factor with i=m−k is zero, and m+q<2q makes the right binomial zero. If m≥q, cancellation of the factorial products proves (2). Thus no expression dividing by m−q is introduced in the zero range.

For q≥0 and n>q, define

    G_q(m)=m(m−q) C(m+q,2q)/(q+1),  m≥q.

G_q(q)=0. The binomial ratio from m to m+1 has denominator m−q+1>0, and direct subtraction gives

    G_q(m+1)−G_q(m)=(2m+1) C(m+q,2q).

Indeed the remaining numerator is (m+1)(m+q+1)−m(m−q)=(q+1)(2m+1). Therefore

    Σ[m=q..n−1] (2m+1) C(m+q,2q)
       = n² (q!)²/((q+1)(2q)!) C(n−1,q) C(n+q,q).       (3)

For q≥n≥1 define the sum as empty. The right side of (3) is also zero because C(n−1,q)=0. This extension uses the second endpoint formula, not an unjustified factorial with negative argument.

Let S denote the unweighted source sum and r=l−1. Substitute (1) and (2), discard only zero terms m<q, and apply (3). The exact rational identity is

    S/n² = Σ[t=0..r] a_(r,t) 4^t C(2k,k)
             Π[i=1..t](k+i)²/(k+t+1)
             C(n−1,k+t) C(n+k+t,k+t).                  (4)

No integrality of S/n² is assumed during this manipulation. The two copies of the original central binomial are essential: their cancellation with (2) and (3) leaves C(2k,k) times the displayed square product.

Here is the entire arithmetic denominator bridge, for every k,t≥0:

    k+t+1 | 4^t (2t+1)!! C(2k,k).                       (5)

Put d=k+t+1 and H=2t+1. For a prime p|d, set a=v_p(d), and let b≥0 satisfy p^b≤H<p^(b+1). For b<j≤a, p^j>H implies p^j≥2t+2, and k≡−t−1 (mod p^j) has remainder R=p^j−t−1 in [0,p^j). Then 2R≥p^j, so

    floor(2k/p^j)−2floor(k/p^j)=1.

Every summand of this form at any j is nonnegative (indeed 0 or 1). Counting prime-power factors in factorials gives

    v_p(C(2k,k))=Σ[j≥1](floor(2k/p^j)−2floor(k/p^j))
                 ≥ max(0,a−b).

For odd p, if b>0 the odd number p^b is one of the factors of H!!, so v_p(H!!)≥b; if b=0 the same bound is trivial. For p=2, v_2(4^t)=2t≥b. To justify the last inequality: t=0 gives H=1 and b=0; for t≥1, 2t+1≤2^(2t) by induction, starting with 3≤4 and using 2t+3≤4(2t+1). Hence the product on the right of (5) has valuation at least a for every p|d. This includes every prime power, not only divisibility by the radical of d. If d=1 there are no primes to check and the claim is immediate.

Finally t≤r=l−1 implies (2t+1)!! divides (2l−1)!!. By (5), every coefficient

    (2l−1)!! 4^t C(2k,k) Π[i=1..t](k+i)²/(k+t+1)

is an integer. All remaining factors in (4) are integers. Multiplying (4) by (2l−1)!! proves precisely the full source divisibility. This is an ordinary universal proof independent of numerical checks. I found no residual uniform lemma or counterexample to it.

Boundary audit: l=1 gives r=t=0 and Catalan integrality C(2k,k)/(k+1); n=l=1 forces k=0 and literal sum 1. At t=0, (5) is the full Catalan divisibility for every k, including powers of two in k+1. At q=n−1 the sum has exactly its last term; at q≥n both sides of (3) vanish. Terms t>m−k vanish on both sides of (2). k=0, n=1 with arbitrary l, and l much larger than n require no exceptions. All denominators q+1 are positive. The candidate's all-degree coefficient recurrence agrees with (1) after c=4^t a and 4u_t+1=(2k+2t+1)².

## Independent exact diagnostics

checker.py was written here without importing or running the candidate checker. It constructs coefficients through exact rational divided differences at squared odd nodes, rather than through the candidate recurrence. It evaluates the literal original sum and independently compares its rational quotient by n² with (4).

checker-evidence.json records PASS for 7,350 literal source/expansion cases (0≤k≤20, 0≤r≤13, 1≤n≤35, k<n); 5,586 interpolated polynomial evaluations; 10,731 cancellation tests including vanishing terms; 2,205 weighted coefficient-integrality tests; 4,140 summation identities including q≥n; 12,261 denominator-grid cases; and 648 targeted prime-power valuations. Targeted d=p^a includes p=2,3,5,7,11,13,17,31, 1≤a≤9, t=0, small t, and higher-degree boundary choices. Large k is tested by the factorial-floor valuation formula without constructing huge binomial coefficients.

The source factor cannot be dropped: l=2,n=3,k=1 gives S=1608≡6 (mod 9); 3!! clears it. This negative control is independently checked. These finite checks help catch indexing/transcription errors and establish no universal theorem on their own.

## SUBSTANTIVE: complete adaptation objection and actual addition

The specific theorem-strength addition relative to the inspected bodies is all odd degrees with modulus n² and weight (2l−1)!!, coefficientwise for every k. It is not simply Chen–Guo's modulus-n conclusion, nor Guo's l=1 theorem. Formula (5) is not printed in either inspected body, and I do not call it an earlier known theorem without a source.

Nevertheless, the complete bridge is routine within exactly the already displayed strategy: expand the polynomial in the shifted quadratic factorial basis as Chen–Guo Section 4 does; retain the explicit coefficient factors 4^t; use Guo's printed exact telescoper rather than stopping at modulus n; clear its sole remaining denominator q+1 using the elementary factorial-floor valuation bound (5). Equations (1)–(5) above supply every step for every parameter. There is no new analytic principle, new summation identity, deeper binomial-product linearization, or separate obstruction left for the source problem. The arithmetic bound uses only the forced carries above the cutoff 2t+1; the missing low valuations are absorbed by the source's very double factorial and powers of four. This explicit coefficient refinement and denominator estimate are the entire additional work.

My campaign judgment is therefore **EXCLUDE as routine complete adaptation**, despite the legitimate stronger endpoint. It is not an exclusion merely because the proof is elementary or short. The objection specifies the applicable classical method, the exact source identity, the additional valuation argument, and the full bridge to the literal endpoint. Root may weigh the uniform denominator insight more highly; if so, it should record that substantive disagreement explicitly and retain a novelty HOLD, rather than treating the printed open label as evidence of novelty. This report does not assert that every elementary conjecture resolution is routine or that the full statement is already published.

## NOVELTY: bounded HOLD independent of eligibility

The source question survives unchanged in the actual 2023 body. That establishes source fidelity, not present-day open status. Current primary arXiv version histories and the three full PDF bodies were checked as above. Current https://lean.up.railway.app/api/data was retrieved independently, SHA256 20c8d27bfad7e13551e7d53bd827821fc6e894061ef9e4d59ca6f103eb522309, identical to the candidate's recent snapshot. Exact identifiers, title phrase, and double-factorial phrase have no hits. Genuine Guo hits concern unrelated coding theory, Fibonacci/Lucas monogenicity, q-deformation problems, and intersection numbers; substring hits in 'unambiguous' and 'contiguous' are not matches. This is a catalog screen, not an audit of all referenced proof bodies. No authenticated current OpenAI GitHub head/tree claim is made.

Two independent guarded Bing RSS searches, exact identifier plus proof, and Guo/conjecture/double factorial, returned HTTP 200 but irrelevant calendar-year/surname/transport/grammar results. Raw bodies, URLs, UTC, hashes and titles are preserved in live/search-*.xml and comparison-evidence.json. These results provide essentially no negative prior-art evidence. The candidate's broader search records are retained with its disclosed native-search deviation. No external search snippet is promoted to a mathematical theorem.

I parsed the full ledger and prior-campaign-context snapshots and reviewed their relevant exclusion/hold entries, candidate history-index snapshots and exact-alias/history screen records. No exact matching recorded outcome was found in these bounded screens. I did not reread 2,550 historical source documents; indexes cannot clear them. The live mutable administrative files are snapshots only and are not bound as scientific inputs. No parked merge-tree/capped interval was reopened. Prior exclusions involving other Guo authors/topics do not subsume this statement. Neither the first 30 nor the nine subsequent credited families is claimed here.

The IJNT typeset predecessor body, the larger Sun/Guo integer-valued-polynomial literature, exhaustive citation successors, MathSciNet/zbMATH, non-English literature and denied current registry routes remain unexhausted. GitHub API/raw/codeload/diff/patch, ScienceDirect and Google challenge routes were not requested. The candidate's two author-hosted 404 responses remain preserved and were not retried. No proxies, TLS disabling, challenges, or access-control bypasses. Current bounded search cannot clear all history, priority, or unpublished work. The eligibility recommendation does not depend on asserting such clearance.

## Formal feasibility and delivery controls

A literal formalization seems feasible using finite polynomial expansions, factorial/binomial identities, prime valuations, and finite sums. The zero convention, natural subtraction, positivity of n and q+1, integrality of the rational endpoint, and valuation-to-divisibility bridge would require explicit proofs. None has been implemented or kernel-checked. No Lean endpoint, axiom audit, manuscript, acceptance, or count is supplied or implied. Given the substantive objection, no such investment is recommended here.

freeze-before.json binds 75 assigned scientific original/copy pairs before review; freeze-after.json verifies both originals and local copies again after the review writes. Final manifest explicitly excludes itself and final-verification.json. A separate guarded verification after final writes checks all manifest bytes and both ends of every assigned pair. provenance.json, FAILURES.md, retrieval.jsonl, comparison-evidence.json and checker-evidence.json document exact provenance, limitations and failures. See final-verification.json for the actual verification outcome rather than inferring it from this plan.
