# r174 scientific record — zero full eligible resolutions

Root owns adjudication. Counts remain 9 additional / 39 total, next 40.
No acceptance, independent eligibility PASS, Lean development or manuscript is
claimed. The partial reductions below are uncredited research notes.

## Selection and exact history screen

The r172 qualified ORIGINAL index is inherited with its qualification and
earlier receipt, without new echo exclusions. All 1,735 inherited paths were
retained; refreshing immediate lane originals added/changed nine records,
giving 1,744 records. Original r111/r112/r113 coverage is respectively 5/2/2
records. The hash/size comparison refreshes only changed/new content metadata;
exact alias screens read the retained bodies. This bounded index is not a
claim to cover every nested original ever created.

The initial Blitvić–Kammoun–Steingrímsson arXiv:2610.29846 lead was rejected
immediately after early-screen.json exposed r108's complete original notes
and the independent packing review. It was not reopened. Its HTTP requests
had already been launched alongside the screen; those bytes are preserved as
unused lead bytes. No inference of freshness comes from their retrieval.

Two fresh-to-this-index claims were then actually body-screened:
(A) Ulfarsson Conjecture 2.9 and (B) Koprowski–Lewis Conjecture 3.1.
The final exact-screen.json searches arXiv/DOI/title/author/statement aliases
across the qualified SUMMARY/discovery/PROOF/review/DECISION originals.
Its sole Ulfarsson-name hit is r105's different, 2024 fully shaded mesh-pattern
claim; its literal content does not concern PAP. No matching earlier
investigation of A or B was found in this bounded original index.

Cached public source catalogues were independently screened, including the
OpenAI CONTENTS and complete pinned preprints tree. Raw-line hits were then
parsed into actual path hits: catalogue-screen.json is not itself a body
clearance. The hypermatrix public proof was found and read; see B below.
No denied GitHub, raw, codeload, patch, ScienceDirect or Google challenge route
was retried. Missing historical merges and current registry coverage remain
parked, not silently cleared by an old path search.

## A. Sustained full target: the eventual reverse strategy

Primary: Henning Ulfarsson, *A Permutation Avoidance Game with Reverse Replies
and Monotone Traps*, arXiv:2603.16004v1, DOI 10.48550/arXiv.2603.16004.
Live abstract and full HTML retrieved at the UTC times in http.jsonl, both
status 200; the abstract lists only v1 (16 March 2026). The HTML itself is
dated August 24, 2026; both facts are retained without inventing a second
version or journal publication. No journal reference was found on that page.

Definition 1.1: a position is X subset S_n. A legal move p in S_k occurs in
some permutation in X and replaces X by those permutations avoiding p.
Normal play applies, including the move that makes X empty. Reversal r
reverses positions, not values. The literal Conjecture 2.9 is

    For every integer k >= 3 there exists n0(k) such that for every
    integer n >= n0(k), Player II wins from S_n by replying to each
    chosen pattern p with p^r. In particular sg(S_n,k)=0.

A failure of some n at fixed k does not refute this eventual quantifier.
Nor does a failure of a particular proposed witness family refute it.

Actual source bodies compared: Definition 1.1; Theorem 2.5 (k=3);
Proposition 2.7 and Example 2.8 (small-n failures at k=4);
Proposition 2.12 and Corollary 2.13 (monotone endgame and sufficient reply
criterion); Definition 6.6, Lemma 6.8 and Propositions 6.9/6.12
(bounded inflation families and finite k=4 tables); Theorem 6.13 (k=4,
n>=10); Section 6.1 (explicit lack of an all-k argument).

Material classical companion bodies: Erdős–Szekeres, *A combinatorial problem
in geometry*, Compositio Math. 2 (1935), 463–470, original Numdam PDF;
Vatter, *Permutation classes*, arXiv:1409.5159 (latest PDF and abstract),
Introduction and Section 3.2, especially the definition of inflation and
Proposition 3.10. The original 1935 geometrical theorem does not by itself
give the game strategy; the precise sequence form appears explicitly in
Vatter's Introduction. Below it is also proved independently.

### Ordinary reduction to a finite separation assertion at each k

For u in S_k, positions i and value gaps j in {0,...,k}, sign e in {+,-},
let J_t(u,i,j,e) insert a monotone block of t new points in the chosen
position/value cell of u. Thus the retained u points still induce u, and
every block point has the same comparisons with every u point. Write Sh_k
for the set of induced classical patterns of length k. For t>=k,

    Sh_k(J_t(u,i,j,e)) = Sh_k(J_k(u,i,j,e)).              (1)

Proof: a k-point occurrence selects r block points, 0<=r<=k, and k-r
retained points. Its order depends only on these retained points, r, the
cell and the sign, not t. Every such selection is possible at t=k and
at all larger t. This proves both inclusions, including r=0 and r=k.
This generalizes the source's Lemma 6.8; it is not a new credited result.

Set N(k)=k+(k+1)^2*(k-1)^2+1. If a permutation pi of size n>=N(k)
contains u, mark one occurrence of u. Its other n-k points fall into
(k+1)^2 position/value cells relative to the marked occurrence. Some cell
contains at least (k-1)^2+1 points. These points contain an increasing or
decreasing subsequence of size k: assign to each point the pair (a,b) of
maximum increasing/decreasing subsequence lengths ending there. Distinct
points have distinct pairs, since for two points in position order either
the first coordinate or the second strictly increases. If both coordinates
were <=k-1 there would be only (k-1)^2 pairs, a contradiction. Selecting
the marked u and this monotone k-subsequence gives J_k(u,i,j,e).
It is a subpermutation of pi, hence avoids every pattern pi avoids.

Consequently, for any forbidden set F subset S_k, legality of u at
n>=N(k) implies the existence of one of these finitely many shadows
T containing u with T disjoint F. Conversely, any such shadow gives a
legal witness at every length n>=2k by (1).

For a shadow T let T* = T union {v^r : v in T}. The following precise
uniform assertion is sufficient for the full source conjecture:

    For every k>=3, every shadow T from some J_k(u,i,j,e), and
    every nonmonotone p in T with p^r in T, there is a shadow S
    from some J_k(v,a,b,d) with p in S, p^r not in S, S subset T*.
                                                               (U)

Indeed, take a reverse-closed, monotone-free F and legal p, and extract
T containing p from a witness of length n>=N(k). Reverse closure gives
T* disjoint F. If T already omits p^r it is itself a separating witness;
otherwise (U) supplies S. Inflating its block to length n-k, then reversing
the resulting permutation, gives a length-n witness containing p^r,
avoiding p, and avoiding F. The reply is legal. N(k)>=(k-1)^2+1, so the
source's Proposition 2.12/Corollary 2.13 closes the monotone endgame.
This would give n0(k)=N(k). **(U) has not been proved for all k.**

The finite scan in diagnostic.py enumerates all u, cells and signs,
constructs exact integer shadow masks, and tests the stronger assertion
also for monotone p. It found zero failed tests:

    k=3: 46 distinct shadows;     72 paired-pattern tests
    k=4: 900 distinct shadows;  1228 paired-pattern tests
    k=5: 7336 distinct shadows; 4056 paired-pattern tests
    k=6: 61816 distinct shadows;11116 paired-pattern tests

The k=6 process completed under the unchanged guard in about 70 seconds,
peak sampled group RSS 57,999,360 bytes. All arithmetic is exact. Independent
selected shadow/stabilization controls in checks.py use rank-by-comparison
and retained-subset/block-count extraction, rather than sorted-dictionary
standardization. They test 510 selected families across k=3..6.
These computations are diagnostics, not an all-order proof. Even adopting
the finite tables as certified evidence would give only parameter instances,
which the task excludes from discovery credit. No such instance is nominated.

### Strongest objection and exact missing step

The strongest complete classical/source objection is that the Ramsey cell
extraction, stabilization, and game criterion are classical pigeonhole and
inflation machinery plus explicit source Corollary 2.13. They do not solve
the game unless the uniform separating shadow assertion is established.
Vatter's substitution decomposition supplies a simple core but does not
give a reversal-separating shadow confined to T*. Source Section 6.1
already proposes extensions by bounded witness families and warns that
general k requires a new idea. The new finite reduction and k<=6 scans
therefore have no independent discovery credit. No counterexample to (U)
was found, much less a source counterexample. No uniform proof is available.
The full target remains unresolved in this lane.

## B. Hypermatrix count: exclude after actual-body comparison

Brandon Koprowski and Joel Brewster Lewis, *Enumeration of Nondegenerate
2 x (k+1) x k Hypermatrices*,
arXiv:2602.22129v1, DOI 10.48550/arXiv.2602.22129. Live abstract has only
v1 (25 February 2026), but lists ECA 7:1 (2027), Article S2R3 and DOI
10.54550/ECA2027V7S1R3. The journal homepage links the actual published PDF,
which was retrieved successfully. The future volume label is reported as
printed; it is not inferred to mean an inaccessible future manuscript.

Both actual arXiv and published Conjecture 3.1 ask, for every positive k,
every prime-power q and every two-layer plane partition P=<lambda,mu>
contained in the source maximal staircase Delta, whether the number of
nondegenerate supported 2 x (k+1) x k tensors over F_q is

    q^(k^2)(q-1)^(2k) product_{i=1}^k
        [k+2-i-lambda_i]_q [k+1-i-mu_i]_q.

The masks are nonincreasing nonnegative integer lists, mu_i<=lambda_i,
lambda_i<=k+1-i, mu_i<=k-i; nondegeneracy is Cayley's second hyperdeterminant
nonvanishing, equivalently full pencil rank over the algebraic closure,
not merely over rational F_q combinations. The published PDF retains the
same formula and open claim; preliminary definition labels have changed.

The cached Omega Problems record names exactly this conjecture. Its actual
companion `KOPROWSKI_LEWIS_COUPLED_DIGIT_BIJECTION.md` provides a constructive
arbitrary-mask, weight-preserving digit bijection, with explicit forward and
inverse maps, local weight identity and telescoping product. Its terminal
proof factors the source's original eligible permutation-pair sum into
the same two q-bracket products. The library note and actual
MaskedHypermatrixCount.lean endpoint connect it to literal supported matrix
pairs; public-body-provenance.json records the cached originals and copies.
The body, rather than a badge or path, is the public-resolution objection.

This lane does not audit the public Lean closure or certify worldwide priority.
The matching full public treatment suffices to withhold discovery credit.
No new hypermatrix proof or counterexample is proposed. Closest Aitken and
Haglund source references were identified in the actual paper but not fetched:
there is no large investment needing them once the exact public body excludes
the target. This is a scope limit, not a claim they supply the full solution.

## Coverage and preservation

HTTP records supply actual UTC dates, status, URLs, final URLs, sizes and
SHA-256. source-hashes.json additionally pins local primary and companion
bytes. Search failures and process deviations are in failures.json; search
receipts are bounded locators, never proof bodies. No new live whole-registry
clearance, exhaustive citation audit, historical capped-merge completion,
MathSciNet/zbMATH search or independent scientific review is claimed.
Campaign ledger/NEXT/prior context copies are archived snapshots only and are
excluded from any live-invariance requirement. Scientific freeze pins local
payload; finalmanifest excludes itself and its verification report. A separate
verifier recomputes every local digest without consulting mutable campaigns.
