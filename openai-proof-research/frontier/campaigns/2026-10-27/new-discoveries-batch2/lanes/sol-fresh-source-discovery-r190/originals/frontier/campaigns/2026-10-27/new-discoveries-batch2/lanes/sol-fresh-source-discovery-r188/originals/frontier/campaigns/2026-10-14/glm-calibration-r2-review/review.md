# Independent parent audit of GLM calibration repairs

**PASS for the assigned finite-algebra calibration repairs.** This audit
concerns the already accepted R019 example and gives no new-result credit.
The subject checker SHA256 is
`7f3d29c316f786db70432b45a5405b317254165894af5d49159c0a1d9e85c08a`.
Original round-1 and round-2 artifacts remain unchanged.

The parent read the complete repair report, the seven changed original
functions, seven added functions, and the mutation dependency table and runner.
An AST comparison confirms the other original function bodies are unchanged;
those inherit the earlier independent baseline audit. The R019 statement,
explicit matrix, polynomial, attainment vectors and irreducibility argument
were reread. This is a targeted repair audit, not a new proof or novelty review.

## Reproduction and independent challenges

An exact copy of the subject checker was run in this separate directory with
Python 3.14.7 and SymPy 1.14.0. It exited 0. All 24 base checks and all four
mutation outcomes match the subject's recorded status, detail and structured
data after removing timing fields. No check raised an exception in that run.
All original provenance hashes still match. The copied checker and stdout
are evidence; they do not replace the independent checks in `audit.py`.

The parent audit independently transcribes N, all four polynomial coefficient
matrices, and x,y from R019. It constructs the two evaluations using SymPy's
Kronecker product, constructs the permutation from the coordinate bijection,
and verifies both builders, J*J=I, F=JPJ*, P x=2y and F(Jx)=2Jy.
The unpermuted squared residual is exactly
`2099/512 - 129*sqrt(14)/256`, nonzero. **D1 resolved.**

After computing the baseline ranks, the same helper is challenged with zero,
a reducible nonzero matrix, and the adjacency matrix of the six-vertex path.
The first two give algebra dimensions 1 and 9; the path has a cyclic e1
(ranks 1,2,3,4,5,6) but algebra dimension 6, separating cyclicity from
irreducibility. A second baseline call reproduces the original ranks, so
cross-input caching is not hidden by call order. The exported 36-word basis
is multiplied independently from the transcribed N and its transpose under
the displayed simultaneous similarity. Its determinant is exactly
`2733816767052433962421431/576460752303423488`. **D2 resolved.**

A non-Hermitian matrix whose principal minors are positive raises the required
ValueError, while positive identity and an indefinite diagonal matrix give
the correct PSD answers. **S1 resolved.** The actual runner is then exercised
with synthetic battery outcomes: expected comparison mismatches return 0;
changing one expected failure to an injected execution exception returns 2.
The battery's exception classification is separately exercised with a raising
function. These are harness tests, not mathematical certificates. **S2 resolved.**

## Corrections and scope

The repair report says “original 21 plus four new” in two places. The code
actually has **three new certificates**, giving 21+3=24. The rewritten tensor
certificate replaces its original counterpart. The recorded total 24 is right.
One mutation-description string writes N^3 as a multiple of e1 e1*; it should
be e1 e6*. The tested identity N^3 N*^3=(7/4)e1 e1* is correct. These are
prose errors; the code and checked results use the correct matrices.

The rationalized irreducibility helper is specialized to the full-rank
calibration/mutants. It attempts a determinant even if a general input's
word-space rank is below 36; it is not a total irreducibility decision
procedure for arbitrary matrices. The zero/reducible controls use the
separate rank helper and are valid. No wider API guarantee is inferred.

The 36 scalar-channel samples remain samples. They do not prove the universal
complex-unit-vector bound. The old theorem's analytic arguments, including
Schmidt overlap, contraction, maximum principle and numerical-range convexity,
remain separate mathematical reasoning. There is no Lean certification of
this checker, no model-reliability conclusion from one trial, and no new
campaign acceptance. The evidence supports GLM implementation of bounded
checks with independent validation; it does not support sole-verifier use.
