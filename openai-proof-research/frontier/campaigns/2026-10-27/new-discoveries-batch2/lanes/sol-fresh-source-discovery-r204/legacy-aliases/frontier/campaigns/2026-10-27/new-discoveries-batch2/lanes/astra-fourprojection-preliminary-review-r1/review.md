# Independent preliminary review: four-projection trace inequality

Review date: 2026-10-28 UTC (2026-10-27 America/Los_Angeles). Solo review; no child agents. Candidate label supplied by the task: commit `74f23e9fb2`, lane `root-fourprojection-r1`. All 46 entries of its `preliminary-review-hashes.json` matched on initial inspection. I did not invoke git or modify the candidate. The supplied commit label itself was not independently checked through git. This is an independent assessment of the frozen proof, not adoption of its self-review.

## Disposition by gate

| Gate | Verdict | Exact scope |
|---|---|---|
| SOURCE | **PASS for arXiv v3; HOLD for published-source comparison** | Fresh latest-version page and PDF, exact Conjecture 6.6 and definitions checked, including visual inspection of p.20. The actual journal conjecture body remains unread after legitimate OA/repository/author routes. |
| MATH | **PASS, ordinary finite-dimensional proof** | The stated argument proves the trace inequality for all finite-dimensional complex orthogonal projections satisfying the two orthogonality and two disjoint-range assumptions, without rank balances. No decisive counterexample or missing hypothesis found within this scope. |
| FORMALCORE | **PASS, eight declarations only** | Fresh local copies compile with the specified absolute Lean binary, warnings as errors, correct pinned mathlib revision, and only the three allowed axioms. Actual printed types inspected. |
| FULL FORMAL ENDPOINT | **ABSENT / HOLD** | No declaration asserts the source theorem for projections or constructs the canonical normalization. This is not a full formal PASS. |
| NOVELTY | **HOLD** | No earlier full resolution or complete subsumption bridge located in the bounded investigation. Material source-comparison and literature-coverage limits remain. |
| SUBSTANTIVE | **Provisionally eligible scope, not accepted** | A full universal source-question resolution would be one substantive family, distinct from prior credited C*-counterexample families. Standard polar identities, scalar helpers, zero-rank cases, and removal of rank balances are not separate discoveries. Novelty and full formal gates remain prerequisites. |

No manuscript gate was assessed. No acceptance, count change, posting, or shared-file edit was performed.

## 1. Exact source and version fidelity

Primary source: Banica–Nechita, *Flat matrix models for quantum permutation groups*, [arXiv:1602.04456v3](https://arxiv.org/pdf/1602.04456v3), p.20, Conjecture 6.6. Fresh PDF SHA-256: `82ea37c2f43e0f2940ce190891306a08881d05149e98a0e743bbb48be5950fd1`, identical to the frozen source. The live [abstract/version page](https://arxiv.org/abs/1602.04456) lists v3, 23 July 2016, as latest. This is a live check on the review date, not a claim about future revisions.

For orthogonal projections P,Q,R,S in M_K(C), the source assumes:

1. PQ=0 and RS=0;
2. ran(P) intersect ran(R)={0}, and ran(Q) intersect ran(S)={0};
3. rank(P)+rank(Q)=rank(R)+rank(S);
4. rank(P)+rank(R)=rank(Q)+rank(S).

It asks for Tr(PR)+Tr(QS) >= Tr(P'Q')+Tr(R'S'), where P' and R' are obtained by conjugating P and R by the positive Moore–Penrose inverse square root of P+R, and Q',S' similarly from Q+S. These are exactly the normalizations used in the proposed proof. Ordinary unnormalized Tr is used; rescaling every ambient trace by the same positive factor does not affect the inequality. Projection means self-adjoint idempotent, not a general oblique idempotent.

The full p.20 statement, its preceding context, and Proposition 6.7 with its p.21 proof were read. The rank equations imply rank(P)=rank(S) and rank(Q)=rank(R). In particular, the source's S=0 special case is degenerate under all six assumptions, although its displayed Halmos argument treats a broader setting. Neither this observation nor that known special case is the proposed discovery. The candidate proves the actual universal inequality, not just a correction to this source peculiarity. It does not prove general quantum Sinkhorn convergence, Conjecture 6.5, strict descent, or an equality classification.

### Published body: still an explicit gap

The journal item is [Advances in Applied Mathematics 83 (2017), 24–46, DOI 10.1016/j.aam.2016.09.001](https://doi.org/10.1016/j.aam.2016.09.001). The publisher landing URL returned HTTP 403. OpenAlex lists an OA published-version PDF at `https://www.sciencedirect.com/science/article/pii/S019688581630077X/pdf`; that exact listed URL also returned 403. Crossref and OpenAlex metadata are not a reading of the published conjecture.

The DOI query to HAL found [hal-02980384v1](https://cyu.hal.science/hal-02980384v1). Both its landing page and full public API record were retrieved. The record has no attached `fileMain_s`; its external full-text link is `http://arxiv.org/pdf/1602.04456`, not a journal copy. The current [Nechita research page](https://nechita.net/research/) likewise links the DOI and arXiv. The linked legacy Banica host `https://banica.u-cergy.fr/` refused connection. An initial guessed author host failed DNS and supplies no evidence. No credential, proxy workaround, challenge bypass, or private access was used.

Therefore the actual printed Conjecture 6.6, possible renumbering, amendments, or added results in the journal body have **not** been compared. No abstract-only clearance is given.

## 2. Independent re-derivation and attacks on the mathematics

Let p,r,q,s be isometric column frames for the four ranges. Write E=[p r]:C^m -> C^K and F=[q s]:C^n -> C^K, allowing m != n and zero column blocks. If E(x,y)=0, then px=-ry belongs to both ranges. Disjointness makes it zero and isometry makes x=y=0. Hence E is injective; likewise F. This is where the disjoint-range hypotheses are needed.

Set G=E*E, H=F*F, A=G-I_m and B=H-I_n. G,H are positive definite on their respective coordinate spaces. In block form,

    A = [[0, p*r], [r*p, 0]],       B = [[0, q*s], [s*q, 0]].

For J=diag(I_rankP,-I_rankR) and L=diag(I_rankQ,-I_rankS), JGJ=I-A and LHL=I-B. These are positive definite because J,L are unitary. Thus every eigenvalue a of A and b of B lies strictly between -1 and 1. No simultaneous diagonalization of distinct noncommuting ambient matrices has been used.

### Canonical positive inverse-square-root bridge

For reduced SVD E=W D Z*, W*W=I_m, Z unitary, D positive diagonal, one has

    EE*=W D² W*,       (EE*)^{dagger/2}=W D^{-1} W*,
    (EE*)^{dagger/2}E=W Z*=E(E*E)^{-1/2}=:U.

The first inverse square root acts as zero on ran(W) perpendicular. This explicitly uses the unique positive functional calculus, not a choice of inverse or of arbitrary Gram–Schmidt frames. Consequently U*U=I_m. For coordinate inclusions i_P,i_R, P'=U i_P i_P* U* and R'=U i_R i_R* U*. The same argument gives V=F H^{-1/2}, V*V=I_n, and the exact Q',S'. This also proves that the four primed operators are projections under the hypotheses.

Put K=U*V and K'=JKL. Both K and K* are contractions: ||U*Vz||<=||Vz||=||z||; apply the same reasoning to V*U. Multiplication by J,L preserves this property. In any independently chosen orthonormal bases, the squared norm of each row and each column of K and K' is at most 1. Square or equal-sized frames are unnecessary.

### Graded relation and correct sign

PQ=0 implies p*q=0: for instance p*q=p*PQq. Similarly r*s=0. Therefore the diagonal blocks of T=E*F vanish and JTL=-T. Since T=G^{1/2} K H^{1/2}, conjugation-equivariance of the **positive** square root gives

    (I+A)^{1/2} K (I+B)^{1/2}
      = -(I-A)^{1/2} K' (I-B)^{1/2}.

For example J G^{1/2}=(JGJ)^{1/2}J; this follows from uniqueness of the positive square root, so it does not require J to commute with G. Diagonalizing A and B separately, and transforming **both** K and K' by the same left and right basis changes, produces for every entry

    u k + v l = 0,
    u=sqrt((1+a)(1+b)), v=sqrt((1-a)(1-b)).

The plus sign in this scalar relation is correct. The transformed l is the entry of transformed K', not entrywise conjugation of k.

### Scalar inequality, including the sign split

Here u,v>0. The relation permits writing (k,l)=(v z,-u z). Thus

    |k+l|²/(|k|²+|l|²)=(u-v)²/(u²+v²)
      =1-sqrt((1-a²)(1-b²))/(1+ab)

when (k,l) is nonzero; the zero case satisfies the resulting identity too. Since |ab|<1, the denominator is positive.

For t=a²+b², the desired coefficient bound is equivalent to

    sqrt((1-a²)(1-b²)) >= (1-t)(1+ab).

If t>=1 the right side is nonpositive. If t<1 and ab<0, use

    (1-a²)(1-b²)-(1-t)²=t(1-t)+(ab)² >= 0.

Both the square root and 1-t are nonnegative, and (1-t)(1+ab)<=1-t. If t<1 and ab>=0, use

    (1-a²)(1-b²)-(1-t+ab)²=(a-b)²(1-t) >= 0.

Now 1-t+ab>=0 and exceeds (1-t)(1+ab) by t ab>=0. All squaring steps have the required sign checks. This proves |k+l|² <= (a²+b²)(|k|²+|l|²). I also checked these polynomial identities independently by symbolic expansion.

### Trace identities and the factor 1/4

Tr(P'Q')=||i_P* K i_Q||_HS² follows from cyclicity of finite rectangular traces; likewise Tr(R'S')=||i_R* K i_S||_HS². In the original block coordinates these are the two diagonal blocks of K. The map K -> (K+JKL)/2 keeps exactly those blocks and zeros the other two. Hence their sum is ||K+K'||_HS²/4. A unitary basis change may destroy the visible block pattern but preserves this norm identity.

Summing the scalar estimates and using **both** row and column bounds, once for K and once for K', gives

    ||K+K'||_HS²/4
      <= (1/4) sum_ij (a_i²+b_j²)(|k_ij|²+|l_ij|²)
      <= (1/2)(sum_i a_i² + sum_j b_j²).

Finally Tr(A²)=2||p*r||_HS²=2Tr(PR), and Tr(B²)=2Tr(QS). These equalities are valid with rectangular off-diagonal blocks. The factor 1/4 from pinching, factor 2 from the two contractions, and factor 2 from each Gram-defect trace combine exactly to the source coefficient 1. This completes the ordinary proof.

### Boundary and hypothesis attacks

Empty individual blocks have identity maps on zero spaces and empty sums. If m=0 then P=R=0, P'=R'=0, and the desired inequality is 0<=Tr(QS); if n=0 use the analogous statement. No division by rank or assumption that P+R is ambient-invertible occurs. The nonempty case permits eigenvalues arbitrarily close to +/-1; only the strict exclusion of the endpoints is used, with no uniform condition-number lower bound.

Dropping the orthogonality hypotheses would genuinely break the theorem. For example in C^3, P=Q=projection onto e1, R=projection onto e2, S=projection onto e3 satisfies both disjoint-range assumptions and both rank balances, as well as RS=0, but has left side 0 and right side 1. It violates PQ=0, so is an attack control, not a counterexample to the candidate. Swapping the two pairs gives the corresponding necessity test for RS=0. If disjointness is dropped, the frame bridge fails: P=R nonzero gives P'=P/2, which is not a projection. I make no extension claim to overlapping ranges.

## 3. Independent execution evidence

`checks/replay.py` copied no compiled candidate object. Fresh `formal/ScalarCore.lean` and `formal/SpectralCore.lean` were byte-copied from the frozen source and compiled in this review lane. `formal/Inspect.lean` prints every declaration and its axioms. The run used `/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean` with `-DwarningAsError=true`. Lean reports 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`. The mathlib checkout's revision metadata reads `d13f23b723b8a846827a245b89c10fc7d3f11612`; no git command was run. Existing pinned dependency artifacts were used, not a source rebuild of upstream mathlib.

The eight names are `FourProjection.denominator_pos`, `sqrt_lower`, `scalar_coefficient`, `weight_inequality`, `real_pair`, `complex_pair`, `weighted_bound`, and `spectral_core`. Every axiom report is confined to `propext`, `Classical.choice`, and `Quot.sound`. Forbidden-proof-token scan passed. The actual types are saved separately in `formal/actual-types.txt` and the full printed terms in `formal/Inspect.log`.

The general `weighted_bound` does not assume its real weights are nonnegative. This is not a defect: its proof only multiplies the row and column upper bounds by the nonnegative squares a_i² and b_j². The spectral application uses nonnegative squared complex norms anyway.

Crucially, `spectral_core` quantifies over arbitrary finite index types and arrays a,b,k,l,u,v. It **assumes** all eigenvalue bounds, square-root weight identities, scalar entry relations, and four families of row/column bounds. This is a meaningful proved finite-array lemma, but it does not construct these objects from P,Q,R,S. There are no projection, trace, Moore–Penrose, frame, diagonalization, or canonical-normalization endpoints in its type. Required bridges remain: range frames and injectivity; the positive pseudoinverse identity; functional-calculus grading; spectral basis transport; contraction bounds; HS/trace and block-pinching identities; final quantified projection theorem.

`checks/independent_checks.py` was written independently of the candidate's diagnostic scripts. It checks canonical ambient spectral inverse roots against SVD polar frames, the graded entry equation, the trace identities, and the final inequality. It ran 901 configurations over ten dimension/rank patterns, including all-zero, zero blocks, equal and unequal total frame sizes, plus five near-singular configurations. On the ordinary cases, maximum bridge error was 8.62e-15, relation error 7.46e-15, and pinching/trace error 1.10e-15; the minimum inequality slack was -8.05e-17, consistent with floating error in exact-zero cases. Near-singular Gram minimum 2.39e-9 produced bridge error about 4.00e-8, honestly retained. A 175561-point scalar sweep and three exact symbolic polynomial identities were also checked. These are diagnostics, never proof substitutes or exact counterexample certificates.

## 4. Bounded novelty and subsumption investigation

All retrieval URLs, dates, HTTP results, bytes, and SHA-256 hashes are in `sources/retrievals.json`. Fresh web searches and source-body files are retained. A live Semantic Scholar query again returned 26 citing records. `sources/citation-coverage.json` gives each record its actual coverage; these records include duplicates. Thirteen records received a relevant-body reading or relevance screen (including preprint/published duplicates); thirteen remain unread or inaccessible. This is **not** a claim to have fully read all 26 papers.

### Closest source successors: actual body comparisons

- [Nechita–Schmidt–Weber, 1911.04912](https://arxiv.org/pdf/1911.04912): Section 3, Lemma 3.1 establishes the standard square-frame inverse-square-root normalization. Conjecture 3.2 asks generic algorithm termination. Lemma 3.4 parametrizes F with FAF*=B under a support condition and minimizes ||F-P_A||_2 via a polar factor. I read these statements and proofs. None compares the two target cross-overlap traces after separately normalizing the two pairs. The optimizer lemma cannot simply be substituted for a proof that a different, quartic objective decreases.
- [Benoist–Nechita, 1608.05811v2](https://arxiv.org/pdf/1608.05811v2): Appendix A, Proposition A.1 and proof give finite-precision termination for strictly positive-definite blocks, using the increasing product of block determinants. Projector blocks are singular and that determinant functional degenerates; moreover, termination of an iteration does not entail monotonicity of this particular quadratic trace potential at each step. No full limiting/monotonicity bridge was found.
- [Weber 2023, Section 3.4, Problem 3.13](https://link.springer.com/article/10.1007/s11785-023-01335-x): actual published HTML asks quantum Sinkhorn convergence. This supports only the stated contextual fact; the larger open problem does not prove that Conjecture 6.6 is open.
- [de la Salle, 2103.14126v2](https://arxiv.org/pdf/2103.14126v2): Theorems 1.1/1.2 give existence of a nearby PVM, with 9 epsilon error in a state-dependent squared norm, plus the commutant/symmetry feature. The target prescribes the positive Moore–Penrose normalization and requires the exact coefficient 1 and four-projection comparison. Existence of some close PVM supplies neither requirement.
- [Brannan–Chirvasitu–Freslon 2020](https://par.nsf.gov/servlets/purl/10185214): published Section 4, Conjecture 4.3 explicitly identifies source Conjecture 5.7; Corollary 4.9 resolves inner faithfulness for N<=5 or N>=10. This is not source Conjecture 6.6.
- [Nechita–Pillet, SudoQ, 2005.10862](https://arxiv.org/pdf/2005.10862): Section 5 describes interpolated alternating normalizations and invokes the preceding optimizer lemma. The inspected algorithm and discussion provide no theorem for the target potential. [Banica–Freslon 1704.00290](https://arxiv.org/pdf/1704.00290), Section 4 Conjectures 4.6/4.7, concerns stationarity and inner faithfulness. [McCarthy 2302.05902](https://arxiv.org/pdf/2302.05902), Theorem 2.3, concerns free orbitals; [Banica 1712.04067](https://arxiv.org/pdf/1712.04067), Section 5, concerns double/triple flatness and transitivity. Actual relevant passages were read, not just abstracts.
- The frozen primary bodies for 2510.15586, 2304.09124, and 1906.10409 received additional relevance screens: magic-isometry completion, polynomial separation for a concrete model, and inverse-limit models, respectively. These were not exhaustive line-by-line readings. The fresh body of [1909.08152](https://arxiv.org/pdf/1909.08152), *Free quantum groups and related topics*, was keyword/section screened; it was not read in full. The separate *Quantum permutations and quantum reflections* 2020 book PDF at `https://vixra.org/pdf/2009.0045v1.pdf` returned 406 and remains unread.

### Wider matrix-analysis comparisons

- [Li, *New Perturbation Bounds for the Unitary Polar Factor*](https://www2.eecs.berkeley.edu/Pubs/TechRpts/1994/CSD-94-852.pdf), Theorems 1–3: actual finite-square/rectangular bounds compare polar factors of two matrices using their difference and inverse smallest-singular-value constants. Such constants are unbounded in admissible nearly intersecting configurations here. Directly applying the displayed bounds to frames does not yield the target uniform coefficient.
- [Li, *Relative Perturbation Bounds for the Unitary Polar Factor*, LAPACK Working Note 83](https://www.netlib.org/lapack/lawnspdf/lawn83.pdf), Lemma 1 and Theorem 1: actual statement and proof read, p.4 visually checked because text extraction has damaged glyphs. For B_tilde=D1* B D2, it bounds polar-factor movement using ||I-D1^{-1}||_F, ||I-D2^{-1}||_F, ||D1-I||_F, ||D2-I||_F. Its Sylvester-equation technique is related to the candidate's spectral reduction and is standard prior art. The natural normalizing factors G^{-1/2},H^{-1/2} introduce quantities that blow up near singular Gram matrices; no specialization giving the sharp trace inequality was established.
- [Frank–Paulsen–Tiballi, math/9812052](https://arxiv.org/pdf/math/9812052), Theorem 1.3 and proof: the polar frame uniquely minimizes sum of squared distances to an original frame among the specified weakly similar normalized tight frames. [Antezana–Chiumiento, Theorem 3.1](https://iam.conicet.gov.ar/wp-content/uploads/sites/222/2025/04/506.pdf) gives best approximation by a rank-k partial isometry in every unitarily invariant norm. These establish standard optimality of polar orthogonalization, not nonexpansiveness for the cross-frame block trace. Minimizing ||E-U||_HS does not by itself minimize ||diag(U*V)||_HS or prove a descent bound comparing it with ||p*r||_HS²+||q*s||_HS².
- [Makarov–Seelmann, 1007.1575v1](https://arxiv.org/pdf/1007.1575v1), Lemma 2.1, Corollary 2.2, and Theorem 4.3: the “four projections lemma” is an algebraic graph-coordinate factorization under ||P-Q_j||<1, followed by an angle-addition relation and a local operator-norm geodesic formula. It is not this four-projection trace inequality. Its equal-rank/local graph assumptions need not hold for the stronger rectangular statement; even in equal ranks its displayed conclusion does not supply the sharp trace bound without further argument.

These comparisons rule out **directly reading the target conclusion from the inspected theorems**. They do not establish that no more ingenious routine corollary or older subsuming theorem exists. No full subsumption bridge was found, so I do not declare NOVELTY FAIL; the remaining coverage gaps also preclude an unconditional NOVELTY PASS.

### Public formal/discovery registries

The live MathDB 332493 record was fetched and read. Its solution array is empty; that is not novelty evidence. The public Ideosphere homepage and embedded paper catalogue were retrieved and screened for the source names, identifier, Sinkhorn, four-projection, and polar terms. The polar matches encountered concerned graph polarity, not polar decomposition. No matching posted claim was located, but this is a catalogue screen, not a replay or reading of every hosted paper.

Public GitHub tree API screens were saved for `google-deepmind/formal-conjectures` at tree SHA `c0c538071a21b36d15f70f5998370eb6a4c31c97` (2250 entries, not truncated) and `the-omega-institute/trureturing` at `d7af67136d4478875778ac6e75eb5fbb8b3693a5` (69 entries, not truncated), together with immutable README fetches. No matching target path was found. The second current tree is very small and is **not** an audit of the older, much larger tree implicated in previous campaign exclusions. These were filename/tree screens, not full source-content searches. The Lean community 1000-theorems page was also fetched. Exact-name/id and GitHub/Ideosphere web searches found no direct posted resolution; search indexing is incomplete. None of these negative screens proves priority.

## 5. Concrete remaining requirements

1. Obtain and read the actual journal conjecture body through an authorized source, or have root explicitly resolve that material source-comparison gap under its acceptance policy. Metadata and the unchanged arXiv file cannot close it.
2. Finish a literal Lean projection theorem with every bridge listed above, then perform the requested fresh strict endpoint replay and independent review. Eight scalar/finite-array declarations cannot stand in for this.
3. Continue bounded novelty review of unread citing works and the closest orthogonalization/perturbation literature, especially if a claimed “known corollary” can be accompanied by an actual theorem and complete sharp-constant bridge.

The frozen argument is mathematically viable. This report supplies no acceptance or discovery-count credit.
