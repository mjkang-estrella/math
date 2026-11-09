# Round 2 numerical audit

DRAFT; diagnostic finite checks, not a proof or acceptance. Zero accepted credit; root alone accepts.

Fresh Python transcription from the hash-bound AntimagicLabel.lean text in the frozen source ZIP, including checked natural subtractions. Every edge was also compared with the independently inherited verifier. Vertex weights were recomputed by adding each edge to both graph endpoints, independently of the identities under test. No Lean, lake or leanchecker was run.

## Coverage and results

All 20 pairs t in {2,4,6,8}, n in {1,2,3,4,5} passed full bijectivity, properness and exact colour-count checks. Each specialized statement below was checked for every applicable pair; repeated evaluations include every parent or pair of slots. Out-of-domain cases are excluded, not counted as passes. Exact data and case lists are in receipts/numerical-audit.json.

- PASS: S1: row sizes t^h; edge count sum t^h; t^n distinct leaf weights. Cases: (2,1), (2,2), (2,3), (2,4), (2,5), (4,1), (4,2), (4,3), (4,4), (4,5), (6,1), (6,2), (6,3), (6,4), (6,5), (8,1), (8,2), (8,3), (8,4), (8,5); 20 evaluations.
- PASS: S1: full bijection [1,m]; independent incidence weights; every edge proper; exact t^n+1 colours. Cases: (2,1), (2,2), (2,3), (2,4), (2,5), (4,1), (4,2), (4,3), (4,4), (4,5), (6,1), (6,2), (6,3), (6,4), (6,5), (8,1), (8,2), (8,3), (8,4), (8,5); 20 evaluations.
- PASS: Frozen text transcription agrees with independent inherited verifier on every edge. Cases: (2,1), (2,2), (2,3), (2,4), (2,5), (4,1), (4,2), (4,3), (4,4), (4,5), (6,1), (6,2), (6,3), (6,4), (6,5), (8,1), (8,2), (8,3), (8,4), (8,5); 20 evaluations.
- PASS: S1/S2/S8: degrees t, t+1,1; diameter 2n; maximal-edge parent weight > m. Cases: (2,1), (2,2), (2,3), (2,4), (2,5), (4,1), (4,2), (4,3), (4,4), (4,5), (6,1), (6,2), (6,3), (6,4), (6,5), (8,1), (8,2), (8,3), (8,4), (8,5); 20 evaluations.
- PASS: S2 depth one: labels 1..t; root t(t+1)/2 > t; t+1 colours. Cases: (2,1), (4,1), (6,1), (8,1); 4 evaluations.
- PASS: S2 Figure 5: rows (1,4),(2,3,6,5); weights 5,6,15; set {2,3,5,6,15}. Cases: (2,2); 1 evaluations.
- PASS: S4 definitions N,q,k,R,Z,m; internal labels [1,N]; leaves [N+1,m]. Cases: (2,3), (2,4), (2,5), (4,3), (4,4), (4,5), (6,3), (6,4), (6,5), (8,3), (8,4), (8,5); 12 evaluations.
- PASS: S4: O_h even concatenated intervals; P_h row permutation; every internal shell label. Cases: (2,3), (2,4), (2,5), (4,3), (4,4), (4,5), (6,3), (6,4), (6,5), (8,3), (8,4), (8,5); 24 evaluations.
- PASS: S4: shell pairs 1..R cover central-hole interval; row one completes [1,N]. Cases: (2,3), (2,4), (2,5), (4,3), (4,4), (4,5), (6,3), (6,4), (6,5), (8,3), (8,4), (8,5); 12 evaluations.
- PASS: S4/S5: sigma lower evens upper odds; delta=-a or k+1-j; both permutations. Cases: (2,3), (2,4), (2,5), (4,3), (4,4), (4,5), (6,3), (6,4), (6,5), (8,3), (8,4), (8,5); 12 evaluations.
- PASS: S4/S5: a parameter, lambda slot families; nonnegative arguments; cancellation p+delta=Z; outer L and middle L+delta. Cases: (2,3), (2,4), (2,5), (4,3), (4,4), (4,5), (6,3), (6,4), (6,5), (8,3), (8,4), (8,5); 6584 evaluations.
- PASS: S4: final parents Z+-[1,k]; a permutes [1,q]; all leaf slot families and block bijections. Cases: (2,3), (2,4), (2,5), (4,3), (4,4), (4,5), (6,3), (6,4), (6,5), (8,3), (8,4), (8,5); 12 evaluations.
- PASS: S5: L=2N+tq+1>m; C=(t/2)L+Z>m; constant final parents; exact Lambda union C. Cases: (2,3), (2,4), (2,5), (4,3), (4,4), (4,5), (6,3), (6,4), (6,5), (8,3), (8,4), (8,5); 12 evaluations.
- PASS: S6: N=2^n-2=2Z; q=Z+1; m=4Z+2; Z>=3; root edges Z,2Z. Cases: (2,3), (2,4), (2,5); 3 evaluations.
- PASS: S6: patched row two (2,2Z-1,1,2Z-2); child sums 2Z+1,2Z-1; weights 3Z,3Z+1,4Z-1 in Lambda. Cases: (2,3), (2,4), (2,5); 3 evaluations.
- PASS: S6: other middle child sums 2Z and translated weights in Lambda. Cases: (2,3), (2,4), (2,5); 3 evaluations.
- PASS: S6: n>=4 Z>=7; row-two weights and first-row adjacency inequalities. Cases: (2,4), (2,5); 2 evaluations.
- PASS: S3 definitions s,q,k,M,beta; root labels and set; exceptional slots and S*. Cases: (4,2), (6,2), (8,2); 3 evaluations.
- PASS: S3: root and S* partition [1,2t]; B=[2t+1,M] has tq entries. Cases: (4,2), (6,2), (8,2); 3 evaluations.
- PASS: S3: every outer pair formula and H. Cases: (4,2), (6,2), (8,2); 15 evaluations.
- PASS: S3: both middle branches; sum 2beta+3k+3+a; tuple D+p-1; parent C. Cases: (4,2), (6,2), (8,2); 15 evaluations.
- PASS: S3: four middle coordinate sets cover beta+[1,4k+2]. Cases: (4,2), (6,2), (8,2); 3 evaluations.
- PASS: S3: root M; sum S*=2s(4s+1)-M=t^2; exceptional weight t^2+2. Cases: (4,2), (6,2), (8,2); 3 evaluations.
- PASS: S3: M and t^2+2 in B; C>t(2t+1)>M; exception>2t and !=M; exact leaf set plus C. Cases: (4,2), (6,2), (8,2); 3 evaluations.
- PASS: S5: every middle child sum tZ; weights incoming+tZ; W formula. Cases: (4,3), (4,4), (4,5), (6,3), (6,4), (6,5), (8,3), (8,4), (8,5); 9 evaluations.
- PASS: S5: geometric identities; N-t<2q and <=2q-2; Z<=q; tZ-N=(t/2-1)(N-t)>=0. Cases: (4,3), (4,4), (4,5), (6,3), (6,4), (6,5), (8,3), (8,4), (8,5); 9 evaluations.
- PASS: S5: N+1<=tZ+f<=tZ+N<=m; W-tZ=(t-1)N/2>N; W<tN=m-t<m. Cases: (4,3), (4,4), (4,5), (6,3), (6,4), (6,5), (8,3), (8,4), (8,5); 9 evaluations.

## Corrections and exact examples

The reported binary depth-three error is corrected in paper.md and PROOF.md (Section 6). The old leaf row (10,14,8,13,9,12,7,11) gives final-parent weights (26,26,22,22), confirmed as a negative control; it cannot support the old claimed constant 26. The frozen formula gives rows (3,6), (2,5,1,4), (10,12,8,11,9,14,7,13), weights (9), (10,11), (24,24,24,24), then the leaf labels; N=6, Z=3, q=4, m=14, C=24, spectrum [7,14] union {24}, nine colours. All printed example numbers were checked.

The t=4,n=3 example is unchanged: N=20,Z=9,q=16,m=84; internal rows (9,18,19,20), (8,10,7,11,6,12,5,13,4,14,3,15,2,16,1,17); W=66, row-one weights (45,54,55,56), 16 parents of weight 219; leaves [21,84], 65 colours. First parent p=8 has a=16, sigma=15, tuple (36,69,52,54), sum 211 and total 219. All these values passed.

## Noncomputational numbers and formula limits

Theorem/lemma/figure numbers, bibliographic years/pages/DOIs, version identifiers, hashes, dates, reported review counts and arXiv identifiers are provenance data, not evaluations of the labelling formula. They remain attributed to the frozen sources and inherited receipts; the numerical audit does not claim to re-prove published lemmas or rerun inherited formal builds or literature searches. The cited odd-q tuple construction is exercised by every depth-two t>=4 case; the even-q average obstruction follows from the integer versus half-integer means. Abstract theorem scope, endpoint signatures and graph transport are inherited formal correspondence claims, not new formal verification. The finite checks do not replace those proofs.

Every line of paper.md containing digits is indexed in receipts/paper-numeric-lines.json to make the mathematical and provenance coverage reviewable. One further formula correction was required: Section 3 outer pairs sum to H=4t+tq+1, not 4t+(t-1)q+1. For t=4 the outer pair (9,20) sums to 29, whereas the old expression gives 26. The definitions of D and C were already structurally correct but inherit H, so correcting H restores their asserted tuple and parent identities. This is corrected in both manuscript sources. All depth-two checks above use the corrected H. The visible errata note is added in Section 7.
