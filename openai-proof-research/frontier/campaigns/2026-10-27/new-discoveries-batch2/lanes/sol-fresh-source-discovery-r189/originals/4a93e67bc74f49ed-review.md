# Independent preliminary review: reflected Steiner H-positivity

Recommendation: **INVEST**, subject to root's substantive adjudication and the publication/novelty limitations below. This recommends further work, not acceptance or a formal PASS. Source fidelity PASS for authenticated arXiv v1; ordinary mathematics PASS; substantive eligibility provisionally favorable; bounded novelty screen clear of an identified matching resolution, but novelty NOT ESTABLISHED globally. Target journal comparison remains LIMITED. Credit 0; 5 additional / 35 total, next 36. Only root accepts.

## Frozen evidence and conduct

All 56 files in root-steiner-reflection-handback-r1/review-freeze.json were independently hashed before copying to `frozen/`, including the manifest itself. This differs from the 55 manifest payload entries. See freeze-before.json and freeze-after.json for exact bytes and hashes. I read the full candidate PROOF.md, SUMMARY.md, discovery.md and provenance.json, registry screen and HTTP receipts. I used my own copy and own checker, not the candidate checker as verification.

Read ancestor/batch instructions, current ledger, prior-campaign context and the supplied prior wreath exclusion/review. The latter's explicit source-lemma bridge is a calibration example, not a transferable exclusion. The first thirty/current five statements were compared by actual scopes (context-read-summary.json). None claims reflected Steiner tensor positivity or a negative H-pair. Outcome 15 is a graph connection–Dirac singular-value comparison, not this tensor; outcome 23 demonstrates that a separate explicit question can qualify without settling its source's main conjecture. Existing elementary counterexample outcomes do not automatically qualify every counterexample. Pinned OpenAI theorems are accepted premises; no upstream truth audit was conducted, and this proof uses none of them.

Only this assigned lane was written. No git, children, shared edits, other-lane edits, contact, posting, uploads, accounts, browser tabs or sibling polling. No Lean build or manuscript work.

## Authentic source and interpretation

Source: Cooper–Du, *Determinants of Steiner Distance Hypermatrices*, https://arxiv.org/pdf/2505.10501v1. Read the definitions on pp1–2, Theorem 2.1 and its cut argument pp2–3, and all of Section 4 pp8–10, including references. Visually inspected complete cached rendered pp9–10 using the PDF skill. The freshly retrieved version-specific PDF at 13:40:02 UTC is 365553 bytes, SHA256 2475bf1990f404e2bd6bd7e5badf618aaa6dca55199b5648d405aa792c06bab5, identical to the frozen PDF. Current abstract metadata, independently retrieved at 13:39:29 UTC, still lists v1, submitted 15 May 2025. The PDF internally says 13 June 2025. Both facts are preserved; no inferred extra revision.

The source defines Steiner distance as the minimum edge count of a connected subgraph containing the set of tuple entries, explicitly suppresses braces, and indexes M over all ordered tuples. Repetitions are therefore included; no requirement of four distinct vertices or division by a permutation factor appears. Lemma 4.2 gives A=2J/n-I. Page 9 explicitly defines C1=M(.,.,.,A.), with the reflected input last. Proposition 4.5 establishes positivity only of C1+C3. The final paragraph p10 explicitly asks all-positive H-eigenvalues for C1, then its even-order extension. This is a genuine mathematical question supporting a proposed strategy, not an invented helper. The k=4 counterexample refutes the all-tree assertion and consequently the extension to every even order; it does not assert failure at each even order.

I independently fetched Qi's actual 2005 paper from https://www.polyu.edu.hk/ama/staff/new/qilq/qi-eigen-1.pdf (312850 bytes; SHA256 13e7d74df455020cfb5fa98186bcbbc6ef0638b5b3e40df789cc757a972ddcae). Read printed pp1303–1304: its definition (2) uses the first free index and coordinate powers, and its positivity equivalence is expressly for supersymmetric tensors. Page1303 also expressly replaces an arbitrary tensor by sym(A) when considering its diagonal polynomial. Thus Cooper–Du's citation does not license inferring a literal nonsymmetric H-eigenpair from a negative quartic. Our independently computed C0001=14/15 and C1000=43/15 exhibit the actual asymmetry. Candidate correctly avoids that inference, proves the literal equations, and separately covers the symmetric polynomial interpretation. This resolves the interpretive loophole without awarding convention-repair credit.

Fresh exact-title/publication/reflection/H-eigenvalue/counterexample searches and the actual current author page found no target journal version. The author page matches the frozen stale page; it cannot establish nonpublication. A January2026 university seminar search result describes the same determinant/diagonalization work, not a settlement. No comprehensive citation-index sweep was available. Target published/latest scope remains a limitation, not SOURCE PASS for an unknown journal body.

## Independent unconditional mathematics

The graph with edges {0,j}, 1<=j<=29, is connected (every vertex reaches 0) and has no cycle (a cycle vertex has degree at least two, whereas every noncentral vertex has degree one). Hence it is an actual 30-vertex finite simple tree. For any terminal tuple, an edge of a tree belongs to its unique minimal connecting subtree iff deletion of that edge leaves terminals on both sides: necessity follows from connectedness; sufficiency follows by taking the union of unique paths between terminals. Repeated terminals change neither assertion. For the star a singleton leaf tuple has distance zero, while any tuple with at least two distinct entries has one required edge per distinct leaf.

For a cut U|V, distributing the finite ordered-tuple sum of four vector coordinates gives its contribution as product of all four total sums, minus product of all four U sums, minus product of all four V sums. The subtractions remove exactly the two disjoint classes that do not cross the cut. Summing over 29 star edges proves the mixed multilinear identity for arbitrary real input vectors. No positivity or diagonal-polarization assumption enters.

Let x0=s+29, xj=-1 for every leaf. Then sum x=s and y=Ax has y0=s/15-(s+29), yj=s/15+1, sum y=s. Since the free index is first and the reflection is last,

    gi = sum_{j,k,h} M_{i j k h} xj xk yh
       = C1(ei,x,x,x).

For a cut at leaf a distinct from i (including all cuts when i=0), the free vector ei has cut-side sums 0 and 1. Its contribution is

    D = s^3 - (s+1)^2(14s/15-1).

For the cut at i when i is a leaf, those sums are 1 and 0. Its contribution is

    E = s^3 - (s/15+1).

Therefore g0=29D and gi=28D+E at each of the 29 leaves, with no unexamined exceptional coordinate. Expanding yields

    30D = d = 2s^3-26s^2+32s+30,
    30(28D+E) = L = 86s^3-728s^2+894s+810.

Set P=29d+(s+29)^3 L. Independent symbolic expansion gives

    P = 86s^6+6754s^5+154536s^4+339356s^3
        -15429914s^2+23848324s+19755960.

P(5)=-85295770 and P(8)=273617240. Polynomial continuity and the strict endpoint signs yield a real s in the open interval (5,8) with P(s)=0. No uniqueness or numerical root is needed. On the closed interval,

    d = 30-48s + 2s(s-5)(s-8) <= -210 < 0.

Indeed s>=5>0, s-5>=0 and s-8<=0. Now s+29>0 and

    lambda = 29d / (30(s+29)^3) < 0.

The centre coordinate is nonzero and every leaf coordinate is -1, so x is a nonzero real vector (in fact all its coordinates are nonzero). The centre equation is g0=lambda x0^3 by definition. P=0 gives L/30=-lambda=lambda(-1)^3, proving all 29 remaining literal H-equations. This is an exact algebraic existence proof with no residual computational premise.

At s=5, g0=-203 and gleaf=-217/3, so x dot g=-14413/3. It independently disproves diagonal positive definiteness. For the fully symmetric tensor representing the same quartic F, minimize F on sum ui^4=1. The sphere is compact, the negative direction rescales to it, and the constraint gradient is nonzero there. Lagrange multipliers give grad F=4mu u^[3]; Euler's identity gives mu=F(u)<0. Thus the alternative interpretation is covered too, as one combined outcome, not extra credit. Neither argument refutes the determinant-sign conjecture for original M; nonvanishing/sign, negativity on J-perp and positivity of C1+C3 are compatible with the witness.

## Independent finite diagnostics

ownchecker.py enumerates restricted-growth equality patterns of the three contracted slots: 15 centre patterns and 37 fixed-leaf patterns. It weights anonymous leaves by falling factorials and sums symbolic polynomials, checking all coefficients rather than interpolating four sampled values. Each pattern's weight counts actual assignments; total mass is 30^3 in each orbit. This is substantially different from the candidate's 3.24M direct contractions. Leaf permutation invariance covers every coordinate, with the centre separate.

Additional checks use graph-path unions for seven selected full reflected-tensor entries including all-equal/repeated indices, demonstrate asymmetry, and compare a full arbitrary-vector contraction on K1,4 with its mixed cut expression. Sampled entries are limited diagnostics, not a comprehensive tensor-entry audit. The script reproduces P's endpoint integers, the d identity and rational quartic exactly. Result: all assertions passed, about 0.03s in the measured section, maxRSS 51996KiB. Hard AS512MiB, CPU35s, alarm45s, outer timeout50s; BLAS/OMP/MKL1. These finite checks corroborate the unconditional argument above.

## Closest prior bodies and current registry scope

Read actual Zheng EJC32(2)(2025)#P2.30 published body: pp1–4 definitions, first-index contraction, original tensor resultant and Theorem7 (tree-independence); p12 full Theorem9 statement and opening explicit contractions (P3 determinant product). Published 23 May2025, DOI10.37236/13741. Those theorems concern det(Sk(T)), not C1. A general resultant identity does not supply a real negative eigenpair after one-slot reflection. The long surgery/resultant proof was not independently certified and is not used as a premise.

Read Cooper–Du EJC31(3)(2024)#P3.4 pp1–2 definitions/nonvanishing statement and p6 Corollary4/conclusion, and compared the frozen arXiv conclusion. Conjectures5/6 and Questions7/8 concern tree-independent original determinant, its sign and original-tensor spectral radius, with connected graphs explicit in the published question. Read the even-order companion arXiv2402.15621 Theorem2.5 and its contradiction setup pp6–7: nonzero original Steiner hyperdeterminant. No inspected statement provides a reflected negative H-pair. These are actual object comparisons, not exclusions based on abstracts or titles.

The frozen MathDB sign-attempt body was inspected for its claimed endpoint and root-product/conjugation mechanism. It concerns original-M determinant sign. Its public posting predates the candidate; exact relative UI dates are not certified. Its correctness was not audited. Even a correct sign proof is logically compatible with this witness, so it is neither a same-question prior resolution nor a license to claim the main conjecture refuted.

Fresh public HTTP at13:39–13:40 UTC advances Omega dev from frozen b38b67f348712cc1d54d5619a0dceb5e57ff1119 to **2ad83ffab7deb22ef8c82288a992d3cac99c17a8**. Compare reports13 commits and returns300 files; the file list is capped and is NOT a complete dev delta. Independently fetched complete trees: D5 31557093b9251dd3c70945afc854d023f05c134c (12547 entries, truncated=false) and Problems b0dfc749b68f250535c96dfe57d4db34e43f6387 (1551, false). Full path/blob comparison identifies four changed D5 files on bilateral product congruences/independent-root coherence and one changed Problems record on Hanna's bilateral product. Internal directory SHA changes are separately retained. This closes the named-scope delta without pretending the capped compare is exhaustive.

Actual closest matching problem-record claims freshly fetched at that immutable head and read: Jana–Mahato–Sivasubramanian path principal-matrix characteristic-polynomial peak refutation (n16), and Zhang–Tian all-tree Steiner diameter/anchored-radius inequality. The latter shares the cut representation of distance, but concludes an extremal terminal-set inequality, not a reflected-tensor eigenvalue claim. The former flattens distance on pairs into a principal matrix and addresses coefficient peaks. Neither subsumes this object. No exact reflected-tensor claim was located to read. No semantic absence follows from that search.

Other heads are unchanged: Omega main d7af67136d4478875778ac6e75eb5fbb8b3693a5; OpenAI7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a; AIM8729eab98bafe409b66c5e39253bf56569a62327; Countdbf673741a54c7dc9d88a6aec0e8148a538f4a3a. Reused the frozen named complete OpenAI preprint/AIM/Count scopes only (13578/3541/183 entries). Path matches include planar Steiner ratio and Presburger Cooper, not this endpoint. Neither whole-dev nor complete semantic literature coverage is claimed. Exact URLs, UTC, bytes and SHA256 are in live-http.json, refresh-http.json and frozen/http.jsonl. No403/429/challenge occurred and no retry/bypass was attempted.

## Substantive assessment, objection and falsifier

The strongest EXCLUDE case is that the source already supplies the cut identity, the star has only two orbits, the resulting algebra is elementary, and the negative quartic plus classical symmetric variational theory already answers the symmetrized reading. The H-pair adds no determinant-sign conclusion and the question is ancillary to that strategy. Formalization difficulty would not make this a substantive discovery. The choice n30 has no minimality, optimality or classification content and earns no separate credit.

The strongest INVEST case is more than an open label: the construction defeats the explicit all-tree positivity speculation on an actual finite tree and supplies all literal nonsymmetric H-equations, which the source's symmetry-based positivity citation cannot give. Its nonzero-sum two-orbit vector must simultaneously meet a common coordinatewise eigenvalue relation and keep that eigenvalue negative. The exact interval crossing supplies this compatibility; neither conditional negativity on sum-zero vectors nor positivity of C1+C3 entails it. The published cut theorem is a representation valid for both positive and negative candidates, not a theorem giving this same-object sign or H-pair. Qi's theorem only converts a negative symmetric form once a negative direction has been established, and does not imply the literal pair.

I found no actual same-object published subsumption bridge eliminating that construction/compatibility step. Accordingly I recommend INVEST at this preliminary stage, with modest claimed depth and an explicit routine objection retained for root. This is not the inference that lack of a bridge proves novelty, nor that every source question merits credit. Under the ledger calibration, an independently valid exact counterexample with a genuine spectrum compatibility step is eligible for further investment unless root judges that remaining step routine. The prior wreath review had an explicit source cycle-product and probability-limit assembly; it is not a generic rule excluding all two-orbit constructions.

Strongest falsifier: an earlier source or current proof giving a negative H-eigenpair for this reflected tensor (or a theorem with an explicit specialization forcing it) would change the novelty/substantive recommendation. A located target published version that removes/answers the question would also require chronology and scope reassessment. Mathematically, a different reflected slot/free-index convention would matter, but the literal source and Qi definition have been checked, and the alternative symmetric reading is separately covered. A failure of the cut-to-minimum-subgraph identity or any coordinate equation would invalidate the proof; neither occurred.

Literal formal feasibility is favorable but unproved: the eventual endpoint must define a real finite star as a tree, its minimum connected-subgraph distance on repeated ordered tuples, A and the literal four finite sums. A generic premise asserting the two cubics is insufficient. The algebra/continuity/strict-IVT steps are routine formal tasks; graph realization and finite-sum contraction are the main bridge work. No Lean endpoint has been compiled or certified. Publication completeness, bounded novelty, independent final formal/manuscript review and strict extracted replay remain acceptance gates. This review changes no counts.
