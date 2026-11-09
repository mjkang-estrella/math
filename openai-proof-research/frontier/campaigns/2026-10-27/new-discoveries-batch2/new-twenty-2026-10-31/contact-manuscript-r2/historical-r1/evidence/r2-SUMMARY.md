# MathDB 365301, formalization r2: partial, zero credit

The literal `refutation : ¬ SourceConjecture` is NOT proved. This packet closes
the inherited analytic gaps and starts P4, but is not an accepted refutation.
The campaign count remains 21/40 beyond the previous 39. Only root can accept.

## Checked progress

`SecondBranch.lean` extracts the slope −3 analytic remainder by a nonvanishing
divided difference, computes h(0) = 3 − 2 i, and proves exact imaginary order
two using scalar restriction, Complex.ofRealCLM and Complex.imCLM. Its
`concrete_orders_six_two` constructs both actual analytic roots of the same
exhaustive factorization, with analytic remainders and exact orders six and two.
There is no conditional branch-existence premise in that theorem.

`BranchBounds.lean` proves simultaneous estimates on a common real
neighborhood: for nonzero x, both roots have negative imaginary parts; their
imaginary distances lie in [|x|^6/4, |x|^6] and [|x|^2, 3 |x|^2]. Their
minimum lies in [|x|^6/4, |x|^6]. These are bounds on actual analytic roots,
not estimates on formal polynomial jets.

`HalfPlane.lean` transfers normalized-root exhaustiveness to ALL roots of the
cleared polynomial R, separating x = 0 and x ≠ 0. Its unconditional theorem
`ContactPilot.half_plane_contact_six : HasHalfPlaneContact R 6` checks the
inherited predicate exactly: boundary zero, positive common constants and
radii, every-root lower bound and an attained upper bound at a small strictly
lower-half-plane root. This closes r1 GAPS items 1–4.

`GraphResolvent.lean` starts P4: the specified Fin 5 simple graph, exact
coloring, explicit root-to-all-vertex walks, nearest-w distance one, the actual
adjacency-minus-color-diagonal matrix, determinant Q and diagonal adjugate N,
and the unconditional total-field identity

`graphFunction candidateGraph candidateColors 0 z w = N z w / Q z w`.

It also proves the exact clearing identity
R(x,w) = x^3 (Q(−1/x,w) − i N(−1/x,w)) for nonzero complex x.
No stable-domain conclusion is inferred merely from that rational identity.

## Missing endpoint

P4 still needs common-divisor reducedness over complex bivariate polynomials,
the reduced stable bidisk certificate, uniform Cayley zero-set comparison,
HasZeroSetContact of order six, exclusion of contact two and the literal
negation of SourceConjecture. GAPS.md gives the exact next polynomial
reducedness obligation and all later bridges. The source definitions were
neither changed nor found unworkable. Source/novelty limitations in the
inherited review remain; no new novelty clearance is claimed.

## Validation and provenance

The final source-only packet was freshly extracted into work/extracted-02.
All nine modules passed sanitized strict Lean 4.34.1 compilation with
`-j1 -DwarningAsError=true`, and leanchecker passed on every module. Six
negative controls failed as expected: wrong slope imaginary sign, a spurious
cleared root, wrong graph distance, false square-root equality, wrong residual
constant and impossible constant-polynomial contact. No control was killed
by a resource cap. Refusal of pre-existing local oleans was separately tested.

There are 122 local declarations including generated ones: SourceContact 39,
QuadraticBranches 19, ExactOrders 15, SecondBranch 9, BranchBounds 3,
HalfPlane 9 and GraphResolvent 28. Thus 73 are inherited and 49 new. Both
audit modules introduce no persistent declarations. All local types and
opaque-inclusive bodies, defining modules, unsafe/partial flags and transitive
axioms were audited. Only propext, Classical.choice and Quot.sound occur;
no unsafe or partial declaration was found. The lossless expression-DAG audit
has no dangling references, duplicate nodes or omitted root expressions.
The inherited audit additionally supplies its original tree-form output.
This checks local modules against the pinned imported mathlib environment;
it is not a fresh kernel rebuild of all upstream mathlib sources.

The final replay made 24 sequential compiler/checker calls. Maximum sampled
private memory was 4,803,207,168 bytes and maximum wall time was 28.63 s.
Every Lean/checker call had a watchdog, two-CPU affinity, CPU 120 s, wall
140 s, sampled private RSS 6 GiB and MALLOC_ARENA_MAX=2. Receipts and full
logs are retained. Earlier combined tree-audit attempts were killed by the
memory watchdog; their failure receipts are preserved. The successful audit
writes directly to a file and represents expression sharing losslessly,
avoiding accumulated compiler messages and repeated tree expansion. No
mathematical declaration was weakened to repair the audit.

All 39 designated input files were hash-bound before and after, copied with
hash identity and verified unchanged. SourceContact, QuadraticBranches,
ExactOrders and Audit remain BYTE-IDENTICAL to r1. Toolchain binary and
manifest hashes are recorded. No children, git, network lookup, browser tab,
shared ledger edit, publication, upload or external message was used. All
writes stayed in contact-formal-r2, and no started job remains at handback.

Deliverables include results.json keyed 365301, GAPS.md, formal/,
STATEMENT-CORRESPONDENCE.md, REPRODUCE.md, source-only packet
contact-r2-source.zip, input bindings, declaration inventory, complete audit,
negative-control logs and replay receipts in logs/. The final packet SHA-256 is
`4a1f0ede821502c4843b5e6a569b62002bfb3e8393fcf70e2f9f6182f3f8c7a9`.
