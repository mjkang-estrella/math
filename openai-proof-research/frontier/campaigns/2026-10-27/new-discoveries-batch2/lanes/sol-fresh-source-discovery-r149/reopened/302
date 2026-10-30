# Full-tree target still unresolved — no nomination

Assigned continuation of r48, solo. Credit remains zero. This lane establishes neither a full-tree proof nor a literal source counterexample. No PROOF.md, Lean, manuscript or eligibility PASS is supplied. The campaign counts and acceptance files are untouched.

## Literal target and exclusions

Ibarra–Landry–Montoya-Vega–Przytycki, arXiv:2311.18059v1, Open Problem 4.2 p12 asks whether Q(T,f) is unimodal for every finite plane rooted tree and every positive-integer leaf-delay vector which, in left-to-right order, decreases weakly to a minimum and then increases weakly. Definitions1.2/1.7 and §2.1, Theorem2.3, Propositions2.5/2.8, examples3.1/3.3/Remark3.4 and all of §4 were read. The question has no fixed height, degree or delay bound. The recursion sums q^r Q(T-v,f_v) over delay-one leaves; surviving original delays decrease with floor1 and newly exposed leaves get1. The one-vertex value is1. We use this displayed recursion, consistently with the source examples and the older Definition3.1; no exploitation of the awkward prose zero condition.

The star {1,2} case is excluded by r48's CLASSICAL-EXCLUSIONS.md. In fact source Theorem2.3 already handles *all* valley-delay stars. The non-valley star counterexamples 114411 and 21412 in source §3 are excluded. The r48 nonsymmetric/non-log-concave six-edge valley example remains unimodal and is not a resolution.

Accepted first30 and current6 families were screened from ledger/prior-campaign-context; none authorizes credit for this partial. r48 discovery, full classical exclusions and checkers were read. Root acceptance alone can change counts.

## New symbolic route: delayed exterior-chain insertion

Write G(n,k) for the Gaussian polynomial, interpreted as0 outside 0<=k<=n. Give non-root vertices their incident edge. A legal order removes descendants before ancestors and places each original leaf v at a position >=f(v). Its q exponent counts incomparable pairs (u,v) with u planar-left of v and u removed first. Comparable pairs contribute **nothing**. This is exactly the literal recursion: each right edge is charged when its left incomparable vertex is removed. Countdown at position t is max(1,f(v)-t+1).

First analyze two paths: left length a, right length b. If right release is1 and left release d, the initial d-1 removals are forced on the right. If d>b+1, Q=0. Otherwise Q=G(a+b-d+1,a). If left release1 and right release d, reflection gives q^(b(d-1)) G(a+b-d+1,b). These are full symbolic identities for this family, not bounded observations.

More generally, let an old plane rooted tree have N edges and all original leaf delays <=d. Attach a new path of a edges as an *exterior root branch*, on either side, giving its unique original leaf delay d. Any legal enlarged order has at least d-1 old removals before its first new-path removal. Before that point old and global positions agree. Thereafter every old release has already occurred. Removing the new-path entries therefore gives a legal old order; conversely every old legal order admits precisely the shuffles in which its first d-1 vertices precede the new path. This is a bijection, not an independence assumption about arbitrary residual trees.

If d>N+1 no shuffle is possible. Otherwise the shuffle weight is G(N+a-d+1,a) for a left exterior branch, and q^(a(d-1)) G(N+a-d+1,a) for a right exterior branch. The old-order exponent is unchanged; all new/old pairs are incomparable, on a fixed side. Thus these factors multiply Q_old exactly, for arbitrary old trees under the stated maximal-release condition.

For a spider (root branches all paths), choose a minimum-release branch. If that minimum exceeds1 the answer is0. Otherwise start with that path, Q=1, then add remaining branches outward in nondecreasing release order. Valley order guarantees each next branch can be taken on a boundary of the already built contiguous interval. Its release is at least every previous release, so the preceding insertion identity applies. The whole spider polynomial is a monomial times a product of Gaussian polynomials, or zero. Hence unequal path lengths and extreme valley releases cannot produce separated modes. This is uncredited structured-family progress, not a claim resolving all trees or a novelty claim for spiders. Standard Gaussian symmetry/unimodality and preservation for products of symmetric unimodal polynomials are classical.

In particular, for three branches of lengths a,b,c with delays(r,1,s), 1<=r<=s,

    Q = q^(c(s-1)) G(a+b+c-s+1,c) G(a+b-r+1,a),

provided r-1<=b and s-1<=a+b, and Q=0 otherwise. Reflection treats r>s.

The competing-prefix expression derived *before* the structured search was

    q^(c(s-1)) sum_i q^(i(b-s+1+i)) G(s-r,i)
        G(a+b+c-s+1,c) G(a+b-s+1,a-i).

Here max(0,s-1-b)<=i<=min(a,s-r). First r-1 moves are middle-branch moves; the next s-r moves use i left and s-r-i middle vertices. The exponent includes the prefix crossings against the still unremoved middle/right branches. q-Vandermonde collapses this sum to the displayed product. The explicit sum initially seemed able to separate modes; its collapse removes that mechanism. Ten asymmetric/boundary cases check both formulas against the literal order DP; they do not prove the identity, whose bijection is given above.

## Full-tree reduction: an exact rank-slice transform

The same route extends to an exact formula for an extremal twig, but the factor ceases to be independent of the old order. This identifies a more concrete remaining problem than unrestricted summand control.

Let an original leaf of maximal delay d be globally leftmost or rightmost. Such a leaf exists for a valley vector. Remove its entire terminal twig of length a, ending at its first branching ancestor p, keeping p and its other children. Assume p is not the root; the root case is the exterior-branch formula above. The old tree T0 has N non-root vertices and inherits its old original leaf delays, all <=d. No new old leaf is created since p had another child. Let h=depth(p), counting edges from root to p. Let R_t(q) enumerate legal T0 orders with p in position t, using the ordinary incomparable-pair exponent. Then

    leftmost twig:  Q(T,f)=sum_(t>=d) q^(a(N-t-h+1)) G(t-d+a,a) R_t(q),
    rightmost twig: Q(T,f)=q^(a(d-1)) sum_(t>=d) G(t-d+a,a) R_t(q).

Proof of the identity: all new twig vertices must precede p. In an old order with p at position t, the initial d-1 old vertices must precede the first twig removal. This requires t>=d. The remaining t-d old vertices before p can be shuffled freely with the a twig vertices. This contributes the Gaussian. All old delays are already released by position d, so the same deletion/insertion legality argument applies. For a rightmost twig the initial d-1 old vertices contribute a(d-1) crossings, and no old vertices after p contribute crossings. For a leftmost twig the old vertices after p contribute a(N-t-h+1) crossings: exactly h-1 of the N-t old vertices after p are strict non-root ancestors of p, hence comparable and uncharged; every other one is to the right and incomparable. The initial prefix gives no crossing in this orientation. Old/old pair weights are unchanged. This accounts for every incomparable pair once, proving the two identities.

Twenty exact small identities (both sides, lengths1/2, delays1..5 including zero cases) validate the transform by independently enumerating all old orders and comparing to the full-tree DP. This is an uncredited helper identity, not a complete unimodality proof.

**Remaining gap:** establish a uniform unimodality-preserving property of these *actual rank slices* R_t, or find a legal old tree/delay vector for which this exact weighted sum is nonunimodal. Neither individual unimodality nor compatible modes of R_t is assumed. The rank distribution records completion time of an internal branch, which exterior root insertion never sees. The formula applies recursively to the full source class, but lacks precisely this ranked control. No theorem for all trees is asserted.

## Directed finite diagnostics and correction

The bounded family run contains36 designed shapes and2064 valley vectors, at most10 edges: unequal path/fork and fork/path pairs, two unequal forks, a fork between paths, and nested combs. Delays are one-minimum step valleys with endpoint choices from {1,2,3,floor(n/2),n-2,n-1}, deduplicated. This targets branch completion competition rather than expanding r48's spider grid. Every result is unimodal, including zero outputs. It is not an exhaustive tree/delay classification or a finite certificate of the universal claim.

A symbolic formula check caught an early checker defect: ancestor vertices were accidentally included in right masks. Those pairs add a fixed comparable-pair shift, so they did not affect unimodality, but the exponents were wrong. Both ancestor directions are now excluded. All2064 cases were rerun and independently compared to a separate literal countdown/tree-right-edge recursion. Three small cases also enumerate *every permutation* and filter legal orders, agreeing exactly with both methods; one is the r48 six-edge witness, used only as a regression. Final JSON outputs contain only corrected exponents. This correction is not a source result.

## Primary comparison, chronology and current registry boundary

Older closest body read: Dabkowski–Przytycki, arXiv:1711.05328, Definition3.1/Remark3.2, Theorem3.4/Corollary3.5 and §4 Theorems4.1/4.4. Its delayed recursion agrees with the intended source recursion. Theorem3.4 relates Catalan-state coefficients to delayed trees; Theorem4.4 gives Gaussian-product/unimodality for states with returns only on top, and Theorem4.1 is the undelayed wedge/product formula. No bridge taking every arbitrary valley-delay tree into that special class is proved here. In particular the known nonsymmetric valley example forbids simply applying a universal symmetric Gaussian-product conclusion to this whole target. These 2017/2019 results precede the2023 source and must be credited; no spider-priority claim is made.

Current public search repeated plucking/anti-unimodal and full-title/proof queries. Leads inspected were the primary arXiv record, author publication listing and older primary paper. Author listing reports Contemp.Math.834(2026),95–108; the final chapter body remains unread. Only arXiv v1 is evidenced in the fetched history. No statement that the final chapter still poses4.2 is made. No public proof/refutation of the full arbitrary-tree question was located in the bounded material inspected; that is not novelty evidence or clearance.

All five live registry heads were fetched successfully at15:01–15:02UTC,29Oct2026. They equal r49's baseline: Omega dev e1d4e12fbc1f1f82e5f88362e931a52c778b4374; other four heads unchanged. Hashed r49 complete named scopes were reused: Omega D5/Problems12552/1551 entries, Omega main69, OpenAI preprints13578, AIM3541, Count183. Target path terms yielded no matches. Registry-screen.json records hashes and exact coverage. This is a path screen, not semantic body absence, whole-dev clearance, or a proof of novelty. No403/429 occurred in this lane; prior failures remain recorded in r48 and are not silently turned into clearance.

Strongest objection: no sign or interlacing theorem for the ranked transform, and no actual nonunimodal in-scope witness. Strongest falsifier for a claimed completion is a legal valley-delay tree with a coefficient descent followed by a later ascent, or a defect in a claimed rank-slice preservation theorem. Only such an exact witness or an all-tree proof can advance this target. No formal investment is warranted yet.
