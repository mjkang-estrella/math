# Unresolved: full fake-Gaussian positivity

Credit 0. No completed eligible ordinary theorem, refutation, Lean endpoint or acceptance nomination. Counts remain 5/30 additional and 35/60 total, as supplied by root. No PROOF.md.

## Literal full target and source chronology

Mona Gatzweiler–Christian Krattenthaler, *A positivity conjecture for a quotient of q-binomial coefficients*, published online 17 December 2025, Ramanujan Journal69(2026), article13, **Conjecture4 and equation(2)**. Actual open-access journal HTML obtained and statement/body read, rather than inferred from the abstract. Its latest arXiv2502.06032v3 PDF was read at pp2–3 and surrounding proofs; original submission9 February2025, latest revision20 November2025. Source URLs:

- https://link.springer.com/article/10.1007/s11139-025-01285-2
- https://arxiv.org/pdf/2502.06032v3

For every pair of positive integers m,n with m≥n and every vector a=(a1,...,an) of nonnegative integers, set

F(m,a;q)= product_{i=1}^n ((1-q^(m+i))/(1-q^i))^a_i.

If F is a polynomial, then every coefficient is nonnegative. There is NO symmetry hypothesis and NO requirement of polynomiality for every m. The all-zero vector gives1. We do not substitute the smaller Gaussian-binomial or symmetric-exponent conjectures.

The actual closest successor, Gatzweiler–Levicán-Santibáñez–Yoshida, arXiv2603.22226v1(23March2026), repeats this as Conjecture1.3. Read actual Proposition3.3 and proof, Theorem3.9 and its Frobenius-bound proof, Corollary3.11, Remarks3.7–3.8/3.12, and Example4.5. Corollary3.11 already proves the target whenever 2n floor(n/2)-2<m, in particular m≥n². Such cases and any further isolated family earn no credit here. Current arXiv metadata fetched; no later version identified there. https://arxiv.org/html/2603.22226v1

## Independent ordinary reductions, without discovery claims

Let E_d(a)=sum_i a_i(1_{d|(m+i)}-1_{d|i}). Cyclotomic factorization and unique factorization give polynomiality iff every E_d≥0. Only d≤n need testing: larger d divide no denominator argument. E1=0. All numerator and denominator factors have constant1; hence the polynomial has constant1, degree D=m sum_i a_i, leading1, and is reciprocal: each factor transforms by q^{-m a_i} under q→1/q, with signs cancelling. These are classical identities, not new results.

For fixed m,n the integer exponent vectors with polynomial F form the additive monoid C∩Z^n, where C={a≥0:E_d(a)≥0}. F(a+b)=F(a)F(b). Therefore positivity on a generating Hilbert basis of this rational cone would imply positivity for every a at that fixed pair. Gordan's lemma supplies existence of a finite Hilbert basis, but provides NO all-n positivity theorem, no effective uniform positive interpretation and no bounded test set across unbounded n. We did not compute or claim complete Hilbert bases. The public large-m bound leaves unbounded n and exponent multiplicity, even though it bounds m for each n.

The obvious stronger construction pairs each denominator degree with a divisible numerator degree, giving a product of geometric sums. It fails even at m4,a=(2,1,1): denominator degrees[1,1,2,3], numerator degrees[5,5,6,7]; both2 and3 can only be paired to6. Polynomiality nevertheless holds. Thus Hall matching of individual divisible factors is too strong.

The successor's stronger sufficient condition replaces divisibility by numerical-semigroup membership. Repeat each denominator i and numerator m+i exactly a_i times to form multisets B,A. Proposition3.3 says that for this degree presentation a regular sequence exists iff for EVERY denominator submultiset I,

#(A∩<set(B_I)>_nonnegative) ≥ #I.

Stanley's standard Hilbert-series formula then gives nonnegative coefficients. A proposal proving only instances satisfying this criterion is a routine consequence of already published results. We sought the missing implication from cyclotomic polynomiality plus m≥n to that criterion. **It is false.**

## Exact in-scope obstruction to the semigroup route

Take m30,n26, exponent1 at indices6,9,10,16,18,20,24,25 and0 elsewhere. Thus

B=[6,9,10,16,18,20,24,25],
A=[36,39,40,46,48,50,54,55].

Nonzero E_d are all1, at d=11,12,13,18,23,27,36,39,40,46,48,50,54,55. All other E_d are0. Therefore F is a polynomial in the literal source domain.

Choose the six-element denominator subset S=[9,16,18,20,24,25]. Exactly five numerator arguments belong to its numerical semigroup:36,40,48,50,54. The others39,46,55 do not. For example, bounded combination enumeration up to55, independently compared with dynamic reachability, establishes this exactly; the complete finite coefficient and reachability checks are in exact_obstruction.py. Consequently5<6 defeats the published sufficient criterion for THIS presentation.

The polynomial has degree240, minimum coefficient0 and maximum121, and is nonnegative. The complete quotient coefficient array is retained, and multiplying it by the full denominator polynomial reproduces the numerator polynomial coefficient for coefficient, including all degrees. This is a genuine obstruction to extending the raw-degree regular-sequence argument uniformly. It is NOT a counterexample to source positivity, NOT a proof that no alternative Hilbert-series presentation exists, and NOT a new credit claim.

An LP was used only to search for this witness. The final exact_obstruction.py uses integers and independently enumerated semigroup combinations, with no solver import. The initial LP run aborted at512MiB with implicit HiGHS threading; this failure is preserved. Explicit HiGHS threads1 succeeded. Floating optimization is not a proof.

## Early falsifiers and bounded diagnostics

check.py uses seed23 and tests9,795 bounded random exponent vectors;4,169 pass exact polynomiality, totaling255,504 coefficients. Checks include reciprocal symmetry, constant/leading1, and exact q1 product identity. No negative coefficient was found. These cases are neither exhaustive nor new theorems. The literal source's m1,n17 vector produces coefficient−1 at q7; independently reconstructed, but m<n, so it cannot refute this target.

cone.py(seed2301) identifies the exact obstruction above; search_obstructions.py(seed2302) makes848 LP solves from1,800 proposed samples and exactly tests two additional candidate quotients, no negative coefficient. Degree cap4000, no degree skips in that run. This does not certify all cone rays or any universal conclusion.

All executable mathematical scripts impose512MiB AS, CPU and wall-alarm deadlines, fixed seeds where randomized, BLAS/OMP1. Numerical LP has explicit solver threads1. No symbolic expansions with uncontrolled memory. Run Python scripts from this lane; check.py and exact_obstruction.py require only the standard library, cone searches additionally require scipy.

## Prior exclusions and current screen

Both AGENTS files, ledger, NEXT, prior context and prior lane summaries were reconciled before target selection. The first30 and accepted31–35 are untouched. BBK, q-Motzkin/Han–Pedon, Tian, RSK, powered-binomial, denominator log-concavity, An–Đoković, Hoggatt, Ku, Fenner, Kahane and Brugidou were not reopened. Fenner is EXCLUDED by Jin's earlier14October AIM proof, per actual independent review; no rediscovery claim is revived.

Agoh's2026 alternating-numerator characterization was briefly screened and rejected: actual source p9 and actual Omega proof explanation give repeated-root counterexample f=(X−2)^2 and the full all-order deletion/finite-difference/reduced-denominator proof. Existing pinned Omega body was fetched and read; its path/commit was already recorded by the08:36:52UTC complete snapshot before this lane. Earliest original addition time was not established; no priority claim is made. The elementary general finite-difference argument would also make a fresh rediscovery ineligible. Shankar and W_n,k interlacing search leads have prior-resolution indications; they were not nominated, and no full independent primary-body exclusion is claimed for those unselected leads.

Mandatory current screen began before mathematical investment. At09:04:50UTC live OpenAI7ef5c0c..., Countdbf6737..., AIM8729eab... agree with the saved complete bases:13,578 preprint entries,183 whole-repository entries,3,541 whole-repository entries, each untruncated. Verified bytes and matching immutable tree IDs are in registry.json. These are complete path screens, NOT all-file semantic reading. Clopen homepage fetched plus bounded site-targeted Gatzweiler/Gaussian search; no relevant resolution lead returned. Homepage is not the complete clopen corpus.

Omega moved to fb587b0e94c9169d5d1076c186dd766253eb5255. The current root-tree request at09:05:18UTC returned403 rate limit. Requests to api.github.com stopped immediately and were not resumed. The earlier complete08:36 snapshot's Blueprint23,087/D5 12,476/Problems1,541 entries were used as explicitly OLD path evidence. **No current complete Omega coverage or full-text novelty clearance.** No1000-entry content listing was treated as complete. No new repository traversal through an alternate host was used; the one raw request was for a previously known immutable Agoh body. Full bounded prior-proof clearance remains HOLD.

## Strongest objection and precise remaining gap

No source result is proposed, so source eligibility fails on absence of a full resolution. The strongest routine-subsumption objection to the attempted mechanism is the explicit Proposition3.3+classical Hilbert-series theorem: any qualifying regular-sequence case is already public. Our exact obstruction shows that mechanism does not automatically cover all allowed exponents, despite polynomiality and m≥n. A uniform cancellation/positive combinatorial representation, a different all-order Hilbert-series presentation, or an exact negative coefficient in the literal m≥n domain is still needed. Additional grids cannot supply this universal step.

No ordinary universal proof, source refutation, independent review, Lean work, public action, count change or nomination. All writes are confined to the assigned lane.
