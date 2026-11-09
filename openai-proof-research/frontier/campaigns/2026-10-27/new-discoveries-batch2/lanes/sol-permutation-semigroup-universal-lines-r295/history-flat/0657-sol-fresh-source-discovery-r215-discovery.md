# Focused solving: small projection constants

Disposition: unresolved, zero nominations. Root alone accepts/counts/stages. No PROOF.md, Lean or manuscript. The helper results below are not candidate resolutions or separate credits.

## Literal target and actual bodies

Beata Deregowska and Barbara Lewandowska, *Projection Constants and Banach-Mazur Distance in Codimension Two*, arXiv:2610.06141v1, Conjecture 1.1, p3. For EVERY integer N and EVERY nonzero real linear subspace V of l_infinity^N, with n=dim V and absolute projection constant lambda(V)<4/3, prove

    d(V,l_infinity^n) <= lambda(V)/(4-3 lambda(V)).

No bound on dimension or codimension is permitted. The source explains equivalence with the same claim for all finite-dimensional real Banach spaces by polyhedral approximation. This lane retains the literal polyhedral statement; no complex-space extension is asserted. A projection is P^2=P with range V; its l_infinity operator norm is its largest absolute row sum. The source identifies absolute and relative constants for these embeddings.

Retrieved actual latest arXiv abstract/version history and PDF from https://arxiv.org/abs/2610.06141 and https://arxiv.org/pdf/2610.06141 . History lists only v1, submitted 5 October 2026 11:12:45 UTC. Read definitions, Conjecture1.1, the rank and projection-diagonal arguments, complete geometric Lemmas2.3/2.4 and Theorems2.2–2.4, and Section3's hyperplane proof, obstruction, column argument and explicit projection. PDF copied and hash-checked before extraction/body reading. Exact retrieval UTC, final URL, response headers, bytes and SHA256 are in http.jsonl and scientific-freeze.json. No journal publication/version is established for this target.

Closest actual proof body: Deregowska–Foucart–Lewandowska, *When is a subspace of l_infinity^N isometrically isomorphic to l_infinity^n?*, https://arxiv.org/abs/2509.16807 and https://arxiv.org/pdf/2509.16807 . History lists v1, 20 September2025 20:56:57UTC. Full six-page body read, including Theorem1, both Lemmas2/3 and complete determinant/block-matrix proof. Target bibliography identifies LAA733(2026)171–177; that journal body was not separately authenticated. The 2025 endpoint lambda=1 and its inverse-minor estimate are credited. Zippin1981/1984, Bernau and the original injectivity bodies were not retrieved/read. Their full quantitative subsumption remains a material gap.

## Full applicable source bridge: column packing

Put L=1+epsilon<4/3. For every rank-n real idempotent P with norm L, let a subset A of [N] be good if there exists k in A with sum_(j in A)|p_kj| >= 2-L=1-epsilon. The source's open column-combining question asks for n pairwise disjoint good subsets. If these exist, choose witnesses k_i and define q_i=sum_(j in A_i)sgn(p_(k_i,j))P e_j. Then q_i lies in V, (q_i)_(k_i)>=1-epsilon, and every row satisfies sum_i |(q_i)_l|<=L because the A_i are disjoint. For any coefficient vector a, choose m maximizing |a_m|. At row k_m,

    |sum_i a_i(q_i)_(k_m)|
       >= |a_m|[2(q_m)_(k_m)-sum_i |(q_i)_(k_m)|]
       >= (1-3epsilon)||a||_infinity.

Also ||sum a_i q_i||<=L||a||. Thus these n vectors are independent, form a basis, and give distortion <=L/(1-3epsilon)=lambda/(4-3lambda) when P is minimal. Minimal projections exist by finite-dimensional compactness (a minimizing sequence of matrices is bounded and the projection/range constraints are closed). This is a complete conditional bridge, not an inference from shortness. The source proves packing for codimensions one/two and for its W_n examples. Those are already-public results, not nominations.

The general sufficient lemma remains EXACTLY: for every N,n with 1<=n<=N, every real P in R^(N x N), P^2=P, rank P=n, ||P||<4/3, the hypergraph above has a matching of size n. It is stronger than the distance conjecture; no equivalence is asserted. The N-2m large diagonal entries of source Lemma2.2 give singleton groups, leaving at most2m coordinates; when m is unrestricted this does not close the problem. Source Proposition3.2 proves that merely finding n disjoint peak sets of range vectors fails in higher codimension; Proposition3.3 proves that this does NOT refute column packing. No source result is excluded on shortness grounds.

## Solving route 1: symmetric cut cubes, closed universally

A plausible counterexample mechanism was many shallow cuts of a cube, hoping that lambda-1 could be much smaller than d-1. This family can be treated in full, rather than just sampled. For every integer n>=3 and every real 1<a<4/3, equip R^n with

    ||x||_E=max(||x||_infinity,(a/n)||x||_1).

Its isometric embedding U into R^(n+2^n) has coordinate rows e_i and (a/n)s for every sign vector s. We prove lambda(E)=d(E,l_infinity^n)=a. The identity between these norms has distortion at most a. The always-applicable injectivity/Hahn–Banach bridge lambda<=d is proved in both actual source bodies: extend an isomorphism to the cube coordinatewise without increasing its norm and compose with its inverse to obtain a projection.

For the reverse bound, average any projection onto U(E) over all signed coordinate permutations. This finite average remains a projection onto U(E), since each conjugate fixes the range pointwise, and its norm cannot increase. Write it as U F. Equivariance forces F on the coordinate-input block to be alpha times the identity: sign flips kill off-diagonal entries and permutations identify diagonal entries. The column of F indexed by a sign vector s must be beta s: the stabilizer of all-plus consists of permutations and fixes only its span; sign flips give every other column. Thus

    F(y,z)=alpha y+beta sum_s s z_s,
    alpha+beta a 2^n/n=1.

An output row indexed by t in the sign block has absolute row sum

    a|alpha|+c_n|1-alpha|,
    c_n=2^(-n)sum_s |sum_i s_i|.

Here c_3=3/2, and c_(n+1)>=c_n by conditioning the next independent fair sign and convexity of absolute value. Hence c_n>=3/2>a. The displayed row norm is >=a(|alpha|+|1-alpha|)>=a. Every projection therefore has norm at least a, proving lambda>=a. Combined with lambda<=d<=a this proves both equalities for the ENTIRE stated family. This is an elementary, fully exhibited bridge excluding THIS proposed counterexample family. It does not exclude the arbitrary source conjecture or establish novelty of the family calculation; no credit is requested.

## Solving route 2: determinant conditioning and a weighted refinement

The actual 2025 Lemma3 has an inverse-principal-minor factor that can be arbitrarily large. This cannot be replaced indiscriminately by a dimension-free constant: P=J/N projects contractively onto constants, and every principal block of Q=I-P of size N-1 has inverse I+J, whose row-sum norm is N. This is an exact all-N argument, not numerical evidence.

A sharper derivation retains rowwise excesses. Choose S of size m=N-n with Z=Q_SS invertible. Such a principal minor exists because the sum of all principal m-minors is1 for an idempotent with eigenvalues m ones and n zeros. Since rank Q=m, its S rows span its row space, so V consists of vectors satisfying x_S=-H x_(S complement), where H=Z^(-1)Q_(S,S complement). Thus coordinate restriction gives d<=max(1,||H||). Define delta_i=sum_j |p_ij|-1 for i in S. From the row norms of P,

    ||(ZH)_i||_1 <= delta_i+|Z_ii|-sum_(j!=i)|Z_ij|.

Multiply by |c_i|, sum, and apply the reverse triangle inequality columnwise to get

    ||c^T ZH||_1 <= sum_i delta_i |c_i|+||c^T Z||_1.

Taking c^T=e_l^T Z^(-1) proves

    ||H_l||_1 <= 1+sum_i delta_i |(Z^(-1))_(l i)|.       (*).

This refinement is a complete auxiliary inequality, not a full source proof. It correctly makes the contractive averaging obstruction contribute zero.

However, the hoped-for sufficient weighted bound <=4epsilon/(1-3epsilon) for arbitrary near-contractive projections is ALSO FALSE. Take N=20, u=(1,...,1), and f having ten entries21/200 and ten entries-1/200. Then f.u=1, P=u f^T is rank-one idempotent, L=11/10 and every delta_i=1/10. For any S omitting coordinate k, Sherman–Morrison gives (I-P_SS)^(-1)=I+u_S f_S^T/f_k. If k is positive, its norm is L/f_k=220/21; if negative the norm is larger (there remain negative indices giving a same-sign diagonal contribution). The minimum weighted norm is22/21, greater than4/7=4epsilon/(1-3epsilon). The range is nonetheless an exact cube of dimension one with minimal projection norm1. This falsifies an auxiliary ALL-projections bound, not Conjecture1.1. Minimality or selection of an appropriate minimizing projection would have to enter; (*) alone cannot deliver that selection. An existential weighted-minor estimate for a suitably selected minimal projection remains a distinct possible route, unproved here. Negative delta values must not be discarded without justification.

## Solving route 3: exact hypergraph matching controls

The checker constructs all good subsets and computes a maximum disjoint packing by exact subset dynamic programming. Inclusion-minimal good sets suffice because shrinking a good set cannot hurt disjointness. It checks135 seeded rational conjugates of averaging projections (ranks2,3,4 in dimensions4,6,8) and238 admissible perturbations of source W_3 in dimension6. Every eligible idempotent has a rank-sized packing. The separate coordinate-minor certificate also passes the first135 cases. Source Proposition3.4's literal rank-two five-coordinate projection is reconstructed using rational u,v,f,g; idempotence and norm13/10 are exact, and adjoining the sixth coordinate gives a packing [{1,2},{3,4},{6}]. All source examples are credited.

Randomized greedy maximal-packing orders found no short packing in these cases. This is NOT a theorem that maximal matchings suffice; no exchange/augmentation proof is available. Conjugation samples around two structured families cannot represent all real idempotents. Two W_3 perturbations exceeded the norm threshold and were not admitted. No finite sample, method falsifier, parameter family, or helper is claimed as a resolution.

## Eligibility, chronology and limits

The bounded compact screen retains1,563 ORIGINAL paths and2,576 reference aliases separately; three changed reports since r212 were frozen. Actual r111–113 remain in the original index, including r111's proof. r207/r209 original unions add no omitted original; r208 has a different alias schema, retained as administrative provenance and not silently promoted. r210 corrected original reports survive in the inherited original index. Exact arXiv, complete title, author-name variants and column-combining terms find no matching earlier candidate. Generic formula fragments have unrelated hits recorded in target-screen.json. Nielsen–Okamura was screened before investment and found already treated in r201, so was not pursued.

Live arXiv ID/title/author searches and actual version histories were retrieved, with UTC/body hashes. These do not authenticate a current complete public proof-registry head/tree/body. GitHub API/raw/codeload/diff/patch denials were respected without retry; ScienceDirect, Google challenge, other inherited denied routes and parked historical capped reconstructions were not attempted. The guessed Foucart publication-page URL returned404; its distinct legitimate institutional homepage was accessible, but supplied no relied-on proof body. Neither search snippets nor an abstract certify unresolvedness. No complete current registry, full subscription-index sweep, all-citer audit or worldwide-priority conclusion is claimed. This is a fresh-to-bounded-screen source target, not certified new-to-literature mathematics.

Strongest substantive objection: the necessary rank-sized hypergraph packing is not proved for arbitrary idempotents, and the two inverse-minor shortcuts demonstrably lose the needed information. Strongest eligibility objection: an explicit quantitative P_lambda problem may already be covered by a stronger older theorem not obtained here. No complete applicable classical bridge to the full conjecture has been found; consequently neither exclusion nor nomination is justified.

All work is confined to r215. Scientific originals/copies and compact immutable reference paths are verified separately after final writes; live mutable NEXT/ledger are snapshots only, not scientific bindings. manifest.json excludes itself and verification-receipt.json explicitly. No shared, git, count, MathDB, browser, external-message/post/upload, child-agent, Lean or manuscript actions occurred. The initial unguarded bounded inventory and two failed helper attempts are recorded candidly in failures/workflow.json.
