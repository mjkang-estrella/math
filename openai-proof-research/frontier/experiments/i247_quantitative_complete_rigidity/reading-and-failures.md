# I247 — reading and failure log

2026-10-12. Read AGENTS.md, sources/upstream.json, R016 in full, finished I242 analytic proof, I245 analytic check and review, I246 contribution analysis and review. Read sources/CONTENTS.md lines 7925–7955 for problem 325 and the two companions. Accepted-count table read at lines 1192–1205. A preliminary overly broad retrieval also displayed TEN-FINDINGS.md lines 1–110; those historical summaries are not research inputs. No live I248/I249 files read. No subordinate agents, code, tests, numerical scans, snapshots, shared edits, staging or publication.

Early decision: do not present the qualitative support-arc extension as new. R016 already contains it. Quantitative rank recovery from nonzero block slack is the intended new bridge. Disk geometry is separately unpaid until an explicit quantitative scalar argument is available.

## Completed source work

Read all retained primary direct/structural excerpts and every retained proof, Jin v2 Sections 1–8 plus Corollary 1 in full, ACV v3 Sections 5 and 7 and Section 11 through Corollary 11.5 in full. Read live ACV Section 9 lines 1428–1758 in full, including the scalar quantitative proof. An initially oversized tool response was truncated; the relevant ranges were subsequently fetched in smaller overlapping portions before any excerpt was retained. Extra trailing portions of ACV Section 10 were displayed but are not retained or used as proof dependencies. The longer I246 Section 11 copy was also partly displayed; only the shorter fully read through-Corollary-11.5 copy is retained.

Independently fetched both pinned raw main.tex files, checked every retained block verbatim, and matched their computed Git blob SHA1s to the exact pinned tree entries. Raw whole manuscripts were not retained, since only the relevant blocks were read. Retained excerpt copies preserve original source attribution and existing extraction boundaries.

## Mathematical pivots and rejected claims

1. Starting from exact isotropy only would merely repeat R016. Pivoted to quantitative hyperplane compression and a minmax estimate with explicit ||X*Y|| error.
2. A pointwise lower bound on |h'| initially seemed necessary. Replaced it with weighted averaging by |q|^2 and the identity integral_Gamma |q| dt=arclength. Thus constants need g and ell, not a separately assumed harmonic-measure or derivative lower bound.
3. Naive product-vector replacement loses epsilon^(1/4) in the scalar evaluation. Exact singular-vector stationarity cancels the mixed terms and improves this to sqrt(epsilon).
4. Ordinary spectrum-to-boundary distance does not directly bound a nonnormal resolvent by delta^(-1). Used the adjugate/singular-value determinant bound (3R)^(d-1)/delta^d instead.
5. A first informal idea for a degenerating example used P=diag((1-t)z,z) on N direct-sum (1-t)N. Rejected: the coefficient channel z also acts on the larger N block, giving an unintended norm-two channel, so the proposed entangled pair was not maximal. Replaced by the explicitly computed shifted-disk stadium family in analytic-attempt Section 7. This correction was made before claiming an obstruction.
6. Scalar near-equality of p(A) gives a nearly reducing nilpotent block of p(A), by ACV. It does not give a block of A when p has critical spectral values or merges spectral points. No inverse polynomial is assumed or invented. The degree-three Crabb equality example itself has p'(0)=0.
7. No quantitative version of Jin's exact rational-collapse/full-lemniscate/hyperbolic-divisibility chain was proved. This remains the precise geometry obstruction. A qualitative compactness modulus or an unexplained effective Lojasiewicz appeal was explicitly rejected as a completed discovery.

## Operational scope and status

Only the specified I247 markdown/JSON files and fully read primary excerpt copies in the specified source directory were written. Utility Python was used for text editing, retrieval identity checks and provenance hashing only. No research code, numerical experiments, tests, scans, snapshots, subagents, public communication, staging, commits or shared ledger edits were performed. No independent gates were run by this research sub-agent; the parent owns them.

Final status: completed explicit quantitative scalarization candidate; quantitative disk rigidity unresolved. Ten accepted of the newly requested twenty remains the supplied count, unchanged by this note.
