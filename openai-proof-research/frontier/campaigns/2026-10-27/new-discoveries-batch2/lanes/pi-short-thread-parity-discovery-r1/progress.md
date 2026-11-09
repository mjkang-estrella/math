# progress — pi-short-thread-parity-discovery-r1

## Resolved: the 19,570 vs 19,232 discrepancy
- Source ancillary `threads/genpieces.cpp` + `threads/data/` downloaded (tarball sha256
  79d65cc6d7bdb7a4e1757401e8aeb35e05b9105d5e1cbc9f7941bb036ae21672).
- Their genpieces enforces "children pairwise distinct" at every rooted vertex but NEVER
  checks twins at thread-INTERIOR vertices (vertices of degree 2 inside internal threads
  of length >= 2). For w=2 internal threads with isomorphic halves fa~=fb, the interior
  vertex has two isomorphic branches -> not twin-free, but their code emits it.
- Verified concretely: their saved list `threads/data/L3_n16.txt` (214 pieces) contains
  exactly 6 non-twin-free pieces (checked with our independent permutation-based
  is_twinfree_indep). True L=3 counts (ours, exhaustively verified vs all 15-vertex trees
  at n=15: 94 == 94, 0 missing): 1,1,1,4,6,13,24,51,94,208,423,904,1888,4041,8541 at n=7..21.
  Their log claims 100 at n=15 (true 94), 214 at 16 (true 208), etc.
- Their QA_n22.log says pieces=10032 at n=22 — breaks their own ~2.15x growth; consistent
  with being the MIXED-class count including the same bug (our true mixed tf(22)=9899;
  10032-9899=133 bogus pieces at n=22).
- CONCLUSION: 19,570 is an OVERCOUNT. True number of twin-free Q11.4-class pieces with
  <= 22 vertices, other than paths = 19,232 (our count; is_twinfree validated against
  independent checker, 0 disagreements on 459 samples; generation validated exhaustively
  vs all trees at n=15 for L3 and n<=20 for mixed).
- Their null result is still logically valid (they searched a superset), pending our own
  verification of the 19,232.

## In progress
- Grundy computation over all 19,232 mixed-class pieces <= 22 vertices:
  violation iff g not in {0,1} or g != E mod 2 (matches their parsolve2 violation test
  (g%2)!=(E%2)||g>1).
- Exhaustive validation of our mixed generator at n=21, 22 (all 22-vertex trees via leaf
  extension) to rule out UNDERcounting on our side.

## Notes
- No C compiler in env; their C++ not runnable; replicated logic in Python instead.
