# Independent preliminary review: EXCLUDE from substantive discovery credit

Recommendation to root: **EXCLUDE** under this campaign's routine-corollary/source-adaptation standard. Mathematical endpoint: **PASS**, literal universal Conjecture 6.1 is false. Prior printed resolution: **not established**. This is a recommendation, not an acceptance/counting action. Counts remain 9 additional / 39 total / next 40. No Lean or manuscript was written.

The decisive reason is the complete low-degree bridge below, reconstructed from the actual source formulas and the older imaginary-pair example. Neither the short length of the final proof nor the existence of a published conjecture decides this judgment. The incompleteness of the prior-art screen is an independent limitation, not evidence of a known proof.

## Source fidelity and literal negation

Primary object: Ostrovskii–Shcherbakov, arXiv:2508.13554v2, printed pp13–16, Proposition 6.1, Corollary 6.1, Definition 6.1 and Conjectures 6.1/6.3. The bound PDF SHA256 is 355675a9058c16dcefa3c6b0299c833e65432de95d68c7030c3d0915241e2fa5. The v1 PDF SHA256 is 381cddeb6ddb7bc1c5f0c24e67abdf36577f439da101635b588bb2793cb3322e. The same unrestricted Conjecture 6.1 is present in both actual bodies. Current arXiv metadata on 2026-10-30 returns v2, published 2025-08-19T06:23:45Z and updated 2025-08-20T03:07:48Z. This checks the metadata-reported current version, not every possible publisher revision.

The source class E_n(D) consists of entire complex-valued g with sup_D |g^(n)| <= 1. The interpolation polynomial has degree < n. Its self-conjugacy definition requires conjugate nonreal nodes and even multiplicity of each real node. Here there are no real nodes, so the second requirement is vacuous. The proposed nodes are distinct. No confluent interpretation is needed. The witness is even a real-coefficient polynomial, so imposing real-entire symmetry would not save the statement.

Conjecture 6.1 quantifies over every integer 0 <= k <= n-1 and every self-conjugate grid in D^n. At z=1 it equates the supremum over all admissible g to |f^(k)(1)|/n!. The later sentence discusses t=n+1 with EVEN k as a verified special case; this is not a hypothesis of the conjecture. n=2,k=1 is within its literal scope. There is no hidden even-k restriction in Definition 6.1, the conjecture, Proposition 6.1 or Corollary 6.1. Even n is consistent with the grid definition and our n=2.

Independently take a=3/4, b=1/2, nodes a±ib and g(z)=z^3/6. Node squared norm is 13/16 < 1; ||g''||_D=||z||_D=1 (also valid for an open disk supremum). The 13/16 in the handoff is squared node modulus, not ||g''||_D. The interpolant is

    Lg(z) = 23z/96 - 13/64,
    f(z) = z^2 - 3z/2 + 13/16,
    g(z)-Lg(z) = f(z)(z+3/2)/6.

Coefficient multiplication proves interpolation exactly; distinct nodes prove uniqueness. At 1 the derivative error is 1/2-23/96=25/96, whereas |f'(1)|/2=1/4=24/96. Hence the admissible error set contains an element larger than the asserted supremum. This disproves the entire universally quantified equality, without computing the true supremum, assuming existence of an extremizer, or invoking the source monomial-reduction theorem. For a classical supremum treatment, subtract the affine Taylor polynomial at zero, which leaves the interpolation residual unchanged. The resulting h obeys |h'(1)| <= 1 and |h(w)|,|h(conjugate(w))| <= |w|^2/2 by radial integration of h''. Thus |(Lh)'| <= (13/16)/|w-conjugate(w)| = 13/16, and every error is at most 29/16. The error set is nonempty and bounded, so its real supremum is at least 25/96. Alternatively the source claim itself asserts a finite least upper bound and is contradicted by this member.

At zero, a=1/100,b=1/2 gives squared norm 2501/10000 < 1 and strictly positive real parts. The slope is -2497/60000, so the derivative error is 2497/60000 > 1/100 = |f'(0)|/2. This also refutes the extra positive-real-part clause. It is the same cubic/two-node family and earns no separate credit.

Conjecture 6.3 concerns a uniform norm on [-1,1], not the value at 1. For the first witness, R'(x)=x^2/2-23/96, whose maximum absolute value on that interval is 25/96. The conjectured uniform right side is sup |x-3/4| = 7/4. Our witness is below that bound; it gives no refutation of Conjecture 6.3 and proves no assertion about its truth.

## Complete routine-source-adaptation bridge

I read Proposition 6.1 and its binomial-shift proof, Corollary 6.1 and its actual definition of Q on p13, together with Proposition 4.1 and its residue/complete-homogeneous remainder identity (26), and Proposition 4.2 on pp9–10. Their hypotheses permit these simple disk nodes and t=3 >= n=2, k=1. Use Corollary 6.1's actual argument 1_n-z^(-1)z_1:n; there is no need to assume the adjacent conjectural reformulation is typographically perfect.

Put c=1-a>0 and shifted nodes zeta=(c+ib,c-ib). Then

    e1=2c, e2=c^2+b^2,
    s_(0|0)=e1, s_(1|0)=h2=e1^2-e2=3c^2-b^2.

Substitute t=3,n=2,k=1 into the DEFINITION immediately before Corollary 6.1:

    Q_(3,2,1)(zeta) = (3e1-h2)/(3e1)
                     = 1 - (3c^2-b^2)/(6c).

At z=1 the corollary identifies this with the ratio between the unnormalized cubic derivative residual and 3 f'(1). Normalizing z^3 by 6 and the quadratic by 2 leaves exactly this ratio. Since c>0, no denominator vanishes. Thus Q>1 iff b^2>3c^2. The original nodes 1-c±ib lie strictly in D iff b^2<2c-c^2. Both conditions hold for every 0<c<1/2 with 3c^2<b^2<2c-c^2. For an explicit one-parameter bridge take b^2=c and 0<c<1/3: node norm squared is 1-c+c^2<1, and h2=c(3c-1)<0. In particular c=1/4,b=1/2 gives e1=1/2,e2=5/16,h2=-1/16 and Q=25/24. This directly reconstructs the candidate's strict violation using the source's printed formula.

The older primary body Ellard–Smigoc, arXiv:1604.05148v1, pp3–5, is relevant for a concrete reason: Example 2.1 takes pairs (i,-i), has e1=0,e2=1 in dimension two, hence h2=-1. It demonstrates the same parity/sign obstruction to transferring real-variable symmetric-function inequalities. Its Theorem 1.4 and Theorem 2.3 proof explain parity-separated Newton inequalities using interlacing and Newton's inequalities on real nonnegative roots. The exact imaginary example alone is NOT our interpolation counterexample: e1=0 would make Q undefined and nodes near evaluation point 1 would be outside D. The explicit c,b inequalities above close both missing bridges. They use only the known degree-two polynomial and the source's own derivative formula; no new bound on Schur quotients or extremal-function classification is needed.

The z=0 clause is even more direct: the same source Proposition 4.2 specializes the cubic slope to (3a^2-b^2)/6, and the known imaginary-pair obstruction survives a small positive a while keeping nodes inside D. The displayed rational choice checks all strict hypotheses. This reinforces that the two witnesses belong to a routine low-degree adaptation, rather than constituting independent advances.

Khare–Tao arXiv:1708.05197v6 Proposition 1.13 pp10–11, restated as Proposition 8.1 p39, has POSITIVE REAL coordinates. I read its proof in Section 8.2, pp43–45: the quotient rule reduces monotonicity to monomial positivity, obtained by skew-Schur expansions and Lam–Postnikov–Pylyavskyy Schur positivity. This does not assert nonnegativity after conjugate-complex substitution; h2 above demonstrates exactly why. Their positive-real theorem neither proves nor refutes Conjecture 6.1 on its own. The source's invocation of an even-k Newton subcase is correspondingly narrower than the universal conjecture.

My substantive judgment is therefore EXCLUDE: after the source explicitly presents normalized monomials and derivative-ratio formulas, the first nontrivial cubic at the smallest grid size, together with the cited imaginary-pair sign pattern, gives the answer by the explicit specialization above. The additional parameter region and recurrence in discovery.md are correct useful exposition, but do not overcome this completed routine-adaptation objection. This is a campaign threshold judgment about the reconstructed bridge, not a claim that a journal article already states this refutation. Root may adjudicate differently, but should assess this exact bridge rather than count proof length or published conjecture status as decisive.

## Bounded prior/source coverage and access limits

Actual body coverage: source v2 pp9–10 and13–16; v1 pp13–16; Ellard–Smigoc v1 pp3–5; Khare–Tao v6 pp10–11,39,43–45. Fresh pdftotext extracts from bound PDFs are retained in evidence/; the v6 contiguous39–45 extract contains extra context not all claimed as detailed reading. Candidate SUMMARY/PROOF/discovery, chronology, source receipts, access/failure logs were read. Candidate checks were bound but not used as the independent checker. Root triage was not used to derive or validate this proof. Frozen references are reused by absolute path/hash, without copying historical trees.

Live requests on 2026-10-30: export.arxiv.org id_list=2508.13554; bounded author/interpolation search (4 results, only target is same-object); self-conjugate/interpolation search (1 unrelated physics result); Crossref title query (5 metadata hits, none exact title). Full queries, timestamps, statuses, response hashes and retained bodies are in access.jsonl and live/. These are metadata screens, not full-text or citing-completeness searches. They located no printed same-object resolution. Crossref rank-limited absence and arXiv metadata are not novelty clearance. The older references predate source v1; our reconstructed bridge is a review derivation on 2026-10-30, not a newly located pre-2025 published proof.

Shadrin1995's original proof body remains UNREAD/inaccessible under inherited ScienceDirect denial. The source's pp14–15 description of real-node spline extremizers is secondary evidence about that theorem, not inspection of its original proof. Real-node results do not directly address our complex grid. Current public-proof-registry heads and historical inaccessible intervals remain uncleared. No GitHub API/raw/codeload/diff/patch, ScienceDirect, Google challenge routes, proxy, TLS disabling, browser or HEAD retry loops were used. These gaps would block a novelty-clear INVEST recommendation; they do not invalidate the independent routine-source-adaptation ground for EXCLUDE.

Inherited writer SyntaxError is preserved by immutable reference to candidate failures.jsonl. This lane had no computation/retrieval failures through report preparation; successful live access is not described as clearance of the inherited denied routes. Final separate verification will preserve any failure in its receipt.

## Formal feasibility only

A literal formal counterexample looks feasible: define two explicit complex nodes and the polynomial interpolant, prove node membership/conjugacy/distinctness, the entire derivative bound, polynomial interpolation uniqueness and derivative evaluation, then contradict the conjectured finite upper bound. Exact rational arithmetic and elementary complex norms suffice for the witness. A source-faithful supremum endpoint needs admissible-set and boundedness/least-upper-bound bookkeeping, not the source monomial-reduction theorem. This assessment supplies no Lean endpoint or certificate. No audit of that reduction theorem is relied on. No formalization or manuscript investment is recommended for campaign credit after this EXCLUDE judgment.

Independent checker.py uses fractions and coefficient convolution, not the scout checker or root computation. checker-result.json records PASS, exact gap 1/96, source Q=25/24, and the uniform-witness distinction. The general parameter bridge is proved above; finite checker samples do not substitute for it. Source hashes are checked before/after, and final manifest excludes itself and verification-receipt.json. Root alone adjudicates and changes counts.
