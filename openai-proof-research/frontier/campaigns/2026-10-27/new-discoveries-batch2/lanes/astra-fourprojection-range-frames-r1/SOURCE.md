# Source and mathematical role

This is a support formalization for Banica–Nechita, *Flat matrix models for quantum permutation groups*, arXiv:1602.04456v3, Conjecture 6.6 (p.20). The cached primary-source text at `../root-fourprojection-r1/sources/four-projections.txt`, lines 969–993, was read directly.

The source inputs are four orthogonal projections P,Q,R,S on a finite-dimensional complex space, with PQ=RS=0 and trivial intersections of the P/R and Q/S ranges. Two additional rank balances occur in the source. Its target compares traces of PR and QS with products of projections normalized by the Moore–Penrose inverse square roots of P+R and Q+S.

This lane proves only the source-frame input construction. It does not prove that trace inequality, the Moore–Penrose identity, any block inequality, or any novelty or acceptance claim. Its lemmas do not require the source rank balances. The same pair construction is reusable for P/R and Q/S, and the same cross-Gram lemma for P/Q and R/S.

Mathematical proof: diagonalize each Hermitian idempotent. Its eigenvalues are zero or one. Retain exactly the columns indexed by eigenvalue one; orthonormality gives pᴴp=I, and summing the retained spectral terms gives ppᴴ=P. Therefore Pp=p, and pᴴv gives the unique coordinates of every vector v in ran(P). For E=[p r], if E(x,y)=0, then px=-ry is fixed by both P and R. Trivial intersection implies px=ry=0; the individual isometries imply x=y=0. Direct block multiplication gives EEᴴ=P+R, the two selector congruences, and EᴴE=[[I,pᴴr],[rᴴp,I]]. Finally Pp=p, Qq=q and Pᴴ=P give pᴴq=pᴴPQq=0 whenever PQ=0.

All sums and matrix products have arbitrary finite index types. No step selects a vector from an empty type or assumes positive projection rank. No step inverts P+R on the ambient space.

Dependencies: copied `HSBridge.lean` and `ProjectionFrames.lean`; pinned mathlib spectral theorem, finite-sum injection, matrix block multiplication, and basic linear-map range facts. Copied-input and primary-source hashes are recorded in `provenance.json`.
