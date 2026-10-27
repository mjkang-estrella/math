# Lin operator-Wielandt norm conjecture — already publicly refuted

MathDB324727 receives no discovery credit. A primary public Lean refutation
predates this run: trureturing commit494409d280d86df6842778425e3ed3f6c9af5dbc,
2026-10-12T21:59:38Z. Actual problem report and Lean source were read/copied;
primary commit API response preserved. Immutable proof:
https://github.com/the-omega-institute/trureturing/blob/494409d280d86df6842778425e3ed3f6c9af5dbc/D5/S3/Quantum/Matrix/OperatorWielandtNormRefutation.lean

Root checked the exact witness independently using rational matrices: both
positive LDL congruences for mI<=A<=MI, partial isometries and orthogonal ranges,
unitality of the two-Kraus map, genuine inverses, product and norm witness.
The squared output norm is5/4 while the conjectured bound is26244/26569<1.
Complete positivity follows directly by Kraus congruences at every matrix level.
The exact matrix inputs and identities are executable in exact_check.py.
No independent replay of the external Lean build is claimed.

Source arXiv1212.5690v1 Conjecture3.4 and its preceding unital2-positivity
convention were read in actual text. The published primary HTML also supplies
that convention and the same conjecture. MathDB's abbreviated statement omits
unitality, but the public witness meets it, so this is not a normalization or
hypothesis loophole. Source Proposition3.3's generic Schwarz-norm failure is a
different preliminary statement; the public theorem addresses literal3.4.

A new congruence-map similarity construction was considered here, but even if
completed it would merely rediscover an already-posted source refutation.
Do not invest in another candidate paper or claim extra credit for stronger
numerical norms, map variants or helper calculations.

Ledger reconciliation:324727 was already excluded by an earlier parent-matrix-screen-r7 check. This recheck adds an original public commit date and saved evidence only; it is not a new research exclusion or discovery. Consult current ledger before relying on older R6 unexamined-target notes.
