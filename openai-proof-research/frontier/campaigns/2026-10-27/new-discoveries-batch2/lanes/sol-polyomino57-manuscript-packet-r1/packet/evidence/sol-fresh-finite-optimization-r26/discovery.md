# Candidate literal refutation of OEIS A395495

Status: exact exhaustive certificate obtained; ordinary source-level proof and independent review NOT completed. No acceptance or credit requested.

## Exact source and endpoint

Peter Exley, OEIS A395495, authored 26 April 2026; rendered public entry retrieved through web search/open on 29 October 2026 before the subsequent direct HTTP403. The rendered page says last modified 10 October 2026, 19:59 EDT. Source: https://oeis.org/A395495 ; history: https://oeis.org/history?seq=A395495 . This is a registry conjecture, not an identified paper with an arXiv/latest/journal version pair. The actual whole entry was readable (141 rendered lines). Its linked solver/code repository https://github.com/pexley-math/oeis-A395495 returns404; its underlying data, authorship metadata and certificates could not be compared. No claim to having read that code.

Define a(n) as the minimum cardinality of a nonempty finite edge-connected C subset Z² such that for every finite edge-connected P subset Z² with |P|=n there exists t in Z² with P+t subset C. Reflections and rotations are NOT allowed in the placement. Holes ARE allowed: the entry explicitly discusses an optimal n=7 container with a hole.

The full source conjecture is a(n)=(n²-n+6)/2 for EVERY integer n>=4 (and a(n)=2n-1 for n=1,2,3). A single eligible n with a smaller universal container refutes this universal formula. It is unnecessary to establish the true optimum or least failing n.

Candidate: n=11 and

    C = {(x,y) in Z² : |x|+|y| <= 5} \ {(2,2),(2,-2),(-2,2),(-2,-2)}.

It has 61-4=57 cells, whereas the asserted formula gives58. Exact exhaustive code checks the literal statement: every fixed11-omino translates into C. It includes all orientations separately and includes shapes with holes. It does not depend on rotating an input during checking. The root is sent to an actual cell of C, so the finite shift set is exhaustive.

## What is mathematically established without enumeration

The diamond has 1+4(1+2+3+4+5)=61 cells. Removing the four indicated distinct cells leaves57. C is edge-connected: from each retained point, reduce a nonzero absolute coordinate toward zero. The only obstructed moves enter one of (±2,±2). At such a predecessor, the absolute coordinates are (3,2) or (2,3); reduce the OTHER coordinate instead, yielding (3,1) or (1,3), then continue toward an axis. Every cell reaches(0,0). Thus C meets all container-side hypotheses.

Any finite connected11-cell P has bounding-box side lengths w,h satisfying w+h<=12: a spanning tree has10 edges and must cross w-1 vertical and h-1 horizontal cuts.

Every such P with min(w,h)<=3 embeds in C by an ordinary argument. C is D4 invariant, so for proof purposes assume h<=3. If h=1, the 11-cell central row suffices. If h=3, w<=9 and the central9x3 rectangle lies in C. If h=2,w<=9, the same rectangle suffices. For h=2,w=10, P cannot occupy all four bounding-box corners. Indeed if a spanning tree of P has v vertical edges and e horizontal edges, then e>=9 and v>=1, while e+v=10. Thus v=1,e=9. If both rows contained both extreme columns, the unique vertical tree edge would force the horizontal path in EACH row to cross all nine column cuts, contradicting e=9. Hence one row misses either its left or right extreme cell. Place the other row on y=0, which has11 cells; place the row missing an extreme on y=1 or y=-1, which has9 consecutive cells. Choose one of the two horizontal shifts of the width10 box so that the absent extreme lies outside that9-cell row. This embeds P by translation alone. (h=2,w>10 is excluded by the box bound.)

The remaining cases have min(w,h)>=4 and w+h<=12. After box symmetry the possibilities are h=4,w=4..8; h=5,w=5..7; h=w=6. I have not supplied a noncomputational universal embedding proof for these cases.

## Exact finite verification, distinguished from ordinary proof

check.py constructs every fixed n-omino, n=1..11, by canonicalized one-neighbor growth. It tests a restricted family of57-cell candidates, namely D5 minus four interior off-axis cells; exactly the stated symmetric candidate survives. Restriction of the SEARCH does not restrict the containment CHECK. All135268 fixed11-ominoes were tested.

verify_independent.py was written separately, imports no search functions, streams rooted animals in the upper half-plane by an ordered forbidden-boundary traversal, and checks all translations sending the distinguished root to C. It writes embedding-certificate.jsonl: one actual input animal and one actual integer translation per line. Counts1..11 are1,2,6,19,63,216,760,2725,9910,36446,135268. Counts are corroboration; coverage does not rest on matching a published count.

audit_certificate.py reads every row, checks literal subset membership, checks distinctness, and checks equality of the normalized terminal family against a fresh neighbor-growth family. The coverage lemma for this family is elementary: every finite connected graph of size>1 has a vertex whose deletion leaves it connected (remove a leaf of a spanning tree); induct downward and reverse the deletion. Normalizing by the separate coordinate minima identifies translations only. Induction therefore proves that growth enumerates exactly all fixed n-ominoes, including holed ones. Full set equality in the audit links this complete family to the certificate, rather than merely comparing cardinalities.

This gives a transparent COMPUTER-ASSISTED exhaustive certificate for the exact source-level counterexample. It is neither sampled numerical evidence nor a Lean theorem. The full ordinary source-level proof gate is not claimed met: the residual finite enumeration has not been replaced by an ordinary geometric argument or kernel-checked finite computation. Consequently no PROOF.md is created. An independent reviewer should decide the evidentiary status of the certificate before any acceptance/formal investment.

## Failed shortcuts, falsifiers and objections

The tree-center theorem only embeds an11-cell animal in the FULL61-cell diamond. It says nothing about avoiding the four holes; it cannot certify57. The box bound alone likewise does not handle the listed nine residual box types. The five shifts of an arbitrary radius4 embedding are not enough to infer hole avoidance; collision sets can be connected with few cells, and additional feasible shifts must be controlled. A proposed triangular container using only coordinate minima was not justified and was abandoned; it is not used.

Strongest mathematical falsifier: a single connected11-cell P without any of the checked57 root-image translations into C destroys the candidate. The saved certificate is inspectable and the verifier fails immediately on such a P. An omitted family in the enumerator would also destroy the universal inference; that is why a separate traversal, exact terminal-set equality, and the ordinary leaf-removal completeness lemma are supplied.

Strongest substantive/novelty objection at full strength: this is a small finite universal-container construction against an extrapolated registry formula, and may be judged too routine under the campaign's unusually strict standard EVEN IF correct and previously unrecorded. No ordinary proof of the hard containment cases exists here. The source's code repository is missing; unpublished or unindexed author data may already contain this shape. The fresh Omega head differs from the snapshot, and the public diff is a bounded update screen, not a freshly fetched complete recursive tree. No worldwide priority clearance, formal proof, independent human review, optimality a(11)=57, or first-counterexample claim is made.
