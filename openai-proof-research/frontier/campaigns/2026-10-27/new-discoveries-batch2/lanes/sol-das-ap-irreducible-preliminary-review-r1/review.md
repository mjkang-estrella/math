# Independent adversarial preliminary review

2026-10-30 UTC. Assigned reviewer works solo. Counts remain **9 additional / 39 total / next 40**; root alone accepts/counts. No Lean, manuscript, git, public, browser, MathDB, or shared-file edits were performed.

**Recommendation: INVEST in the literal finite refutation, with published-source and bounded-prior-art holds before acceptance.** Theorem 1 of the frozen `discovery.md` is a complete mathematical refutation of arXiv:2112.00442v3 Conjecture 5.1. An unknown extremal maximum does not make that refutation partial. No requirement to solve Conjecture 5.2, determine f(n), prove extremality at n=5, or prove the ancillary 6n−6 bound belongs in this assessment. One family, at most one eventual credit.

| Gate | Decision | Reason |
|---|---|---|
| SOURCE | PASS for the exact v3 source; HOLD for identity with the final journal wording | Actual definition p10 and Conjecture 5.1 p22 read; journal body unread |
| MATH | PASS | Exact n5 witness, every deletion, and general cut proof verified |
| SUBSTANTIVE | Provisionally eligible; no demonstrated exclusion bridge | Full negation of a stated universal conjecture; no located classical/source theorem already supplies this signed construction |
| NOVELTY | HOLD, bounded positive evidence only | No prior refutation located in inspected bodies; target journal/thesis, complete citing literature and current public registry heads remain unverified |
| FORMAL-FEASIBILITY | Favorable, unexecuted | Literal Fin 5 source endpoint can use finite cuts and paths, with no analytic/AP-eigenvalue bridge |

## Exact source and signed semantics

Target: Sunil Das, *Sign patterns that allow algebraic positivity*, arXiv:2112.00442v3, submission history v3 22 March 2022 (PDF title page dated March 23), journal reference LAA 653 (2022), 151–182. Primary PDF SHA-256 is `c7ebbffde1cd95c6cf363b9627d3dbd2311d066d0156fffd5a68e6df21198379`. Frozen `frozen/frozen/2112.00442v3.pdf.txt` pp1–2, 10–12 and 22–23 were read, including actual proofs of Lemmas 3.9–3.10. File hashes and original/copy pairs are in `freeze.json`.

Conjecture 5.1 asserts: if A is minimally AP-irreducible of order n with zero diagonal, it has at most 2n−2 nonzero entries. On p10, AP-irreducible explicitly means A is irreducible, every row and column contains a plus, and B_A is irreducible. Minimal means that replacement of any nonzero entry by zero destroys AP-irreducibility. No hypothesis that A allows algebraic positivity is present. The later remark about all *known algebraically positive matrices* does not restrict the conjecture's preceding universal quantifier. Conjecture 5.2 separately asks for equivalence with allowing algebraic positivity.

A− retains negative entries, rather than their positive magnitudes; B_A=A+−(A−)^T has nonnegative support. Thus its arc i→j is present when a_ij=+ OR a_ji=−. If both hold, the two contributions reinforce, rather than cancel. Numerical representatives +1/−1 give value 2 in this overlap case; their sign is still plus. `check.py` tests this explicitly. No opposing signs occupy the same cell in the proposed pattern. Ordinary matrix irreducibility means strong connectivity of nonzero support; equivalently every nonempty proper vertex set has an outgoing edge. The reducible-block definition and digraph equivalence are also stated explicitly on p2 of Abagat–Pelejo's actual preprint body.

## Independent proof and finite witness

The literal n5 pattern (order x,x′,y,y′,s) independently entered into `check.py` is

```
0 + 0 0 +
+ 0 0 0 -
0 0 0 + 0
0 0 + 0 -
0 - + - 0
```

It has six positive and four negative entries, hence ten, exceeding eight. A− is symmetric, so A and B_A have identical support before deletion. Both contain the spanning bidirected path x↔x′↔s↔y′↔y. Positives cover every row and column. Here is a complete deletion certificate (indices 1-based):

| Deleted cell | Obstruction sufficient to destroy AP-irreducibility |
|---|---|
| (1,2)+ | column 2 has no plus |
| (2,1)+ | row 2 has no plus |
| (3,4)+ | row 3 has no plus |
| (4,3)+ | row 4 has no plus |
| (1,5)+ | column 5 has no plus |
| (5,3)+ | row 5 has no plus |
| (4,5)− | A has no outgoing edge from {3,4} |
| (5,4)− | B_A has no outgoing edge from {3,4} |
| (5,2)− | A has no outgoing edge from {3,4,5} |
| (2,5)− | B_A has no outgoing edge from {3,4,5} |

The independent checker uses integer matrices and two reachability searches per strong-connectivity test, not the worker's dictionary code, SciPy, MILP, or random search. It recomputes the entire AP predicate after every deletion, saves all failed conditions in `check-results.json`, and checks the displayed matrix equals the separate family generator at n5. All pass. Initial A/B support equality must NOT be assumed after deletion of a negative entry: recomputing B_A is essential and is done.

For completeness, here is the general proof checked independently. Let m≥0, take distinct vertices x,x′,y,y′,s1,…,sm, and set p0=y′, p1=sm,…,pm=s1,p(m+1)=x′ (when m=0 simply p0=y′,p1=x′). Put plus signs on x↔x′, y↔y′, x→si and si→y; put minus signs in both directions on consecutive p's. Positive cells involve x or y, negative cells involve neither, so there are no sign conflicts or loops. There are 2m+4 positives and 2m+2 negatives, total 4n−10, n=m+4. The displayed bidirected spanning path proves irreducibility of both support digraphs. Positives give a plus in every row and column.

Each plus has a unique-plus row or column, exactly as in the six types in the witness table. For t=0,…,m put U_t={y,p0,…,pt}. This is nonempty and excludes x,x′. Every positive arc whose tail lies in U_t ends at y or y′ within U_t. Among negative arcs only pt→p(t+1) leaves U_t; all others stay inside or enter. Deleting the negative cell (pt,p(t+1)) therefore destroys strong connectivity of D(A). Deleting the reverse cell (p(t+1),pt) destroys the same unique outgoing edge in D(B_A); no positive cell supplies it. These cases exhaust all negatives. Every deletion fails, proving minimal AP-irreducibility for all n≥4. At n4 the pattern has six entries, equal to 2n−2; n5 is the **first violating member of this family**. For n≥5 the excess is 2n−8>0.

The independent finite checks cover n=4,…,40 and all their deletions and outgoing cuts; they illustrate, but do not replace, the quantified proof. The stronger claim that no smaller-order counterexample exists relies on the worker's exhaustive n4 result plus smaller-order reasoning, and is not needed or independently certified here. The review does not adopt the MILP optimum claims.

## Classical/source adaptation and substantive credit

The closest actual target-source proof is Lemma 3.10, not just a metadata description. Its extra assumption forbids positive edges between distinct irreducible components of A+. Its proof decomposes A into positive irreducible blocks, contracts the negative interblock edges to a minimally irreducible matrix X, and adds the bounds (2m−2)+Σ(2n_i−2)=2n−2 using Lemma 3.9. For n≥5 our positive components are {x,x′}, {y,y′}, and the singleton si; x→si and si→y cross those components. The extra assumption is false. That proof cannot be applied. At n4 it does apply and the count agrees.

The classical 2n−2 theorem concerns a digraph minimal for *one* connectivity predicate. Our pattern is minimal for the conjunction of plus coverage, A connectivity, and B connectivity. In n5, removing (5,4)− leaves A strongly connected but breaks B connectivity; conversely deleting (4,5)− breaks A. Ordinary minimal irreducibility and minimal AP-irreducibility cannot be identified. A complete proposed exclusion by that theorem would have to construct the ten signed entries from a previously proved object satisfying the exact three-predicate deletion property, including reversal of negative cells. The inspected theorem and source proof do not provide that bridge.

Abagat–Pelejo, arXiv:1806.09641v2 (16 January 2019), pp2–4, Theorem 4 and its actual eigenvector proof, establishes a *necessary* B_A condition for allowing AP: a reducible B_A supplies a block-sign obstruction and incompatible positive left/right eigenvector products. It does not assert this condition is sufficient, classify minimal AP-irreducible n5 patterns, or construct an oversized minimal example. Its order-three classification cannot itself be an n5 refutation. Das's 2412.06379v4 (13 December 2025), introduction, Theorems 3.14–3.15 with proofs, and conclusion were inspected. Those results classify patterns *requiring* AP whose underlying undirected graph is a cycle, using eigenvalues, sign nonsingularity and adjugates. F5's underlying graph has seven edges and is not C5. No complete adaptation from those proof bodies supplies the present refutation.

I therefore have no explicit complete known-result adaptation justifying EXCLUDE. Quick random discovery, a small witness, elementary cuts, and a standard SCC algorithm do not themselves demonstrate routine-corollary status. Provisionally this is a substantive conjecture refutation, subject to root's credit decision and prior-art holds. Neither its family extension nor an optional sharper extremal theorem earns separate credit.

## Access, chronology and novelty limits

`retrieval/http.jsonl` records exact URLs, UTC times, status, lengths and SHA-256 for each new request. All responses were frozen and compared before scientific reading. Original scout request/provenance/extraction logs and failure outputs are separately frozen. Current arXiv query on 2026-10-30 returned 17 entries for the bounded exact phrase “algebraic positivity”; the only directly relevant later listed paper is 2412.06379v4. This is a small phrase search, not a complete citation search. The fresh Semantic Scholar citing-body request returned **429**, preserved and terminal, with no retry.

The target journal on ScienceDirect remains unread: inherited denied route was not requested. ISI journal-articles/2892 is only metadata/abstract, not a journal proof body and not evidence that the exact numbered conjecture wording survived. The IIT Guwahati thesis1917 frozen page labels both PDF links “Request a copy” with “Restricted bitstream”; its full 19.46 MB body was not fetched or read. No endpoint workaround or request-a-copy mutation was made. A 2021 thesis predates v3 and is potentially important; metadata does not clear its content. No accepted version of the target was obtained in this review.

A distinct lawful publisher route was attempted for the closest predecessor: Crossref identifies ELA DOI 10.13001/1081-3810.3862 and its publisher PDF URL. HTTP200 returned 421728 bytes, SHA-256 `3a74438e8be6a2ec74c36c019b11ff7599f1d1926de72d15c04aed895a2bdab9`. Poppler reported malformed TJ operators and extracted only running headers. First four pages were rendered and visually inspected: they likewise show only journal headers, so this response does not yield a readable published proof body. Failure is preserved in text, render stderr, PDF and PNGs; the actual readable comparison above uses the frozen author's preprint, not these blank pages. No conclusion about unpublished differences follows.

Current GitHub/raw/API/codeload/diff/patch routes and Google challenge routes remain parked, as instructed. No current public proof-registry head or complete historical interval was obtained; no claim of registry clearance or exhaustive 2026 priority is made. Prior inaccessible historical intervals were not revisited. Administrative snapshots contain all nine accepted batch items and thirty prior items; those were loaded and inspected for context, not treated as scientific proof. The scout reports zero history-screen hits; its global history scan was not rerun. No accepted item in these ledgers is identified as the same signed-pattern family, but this does not clear all unaccepted historical lanes.

## Concrete finite formal plan (no runs)

Define `Sign` with zero/plus/minus and literal `A : Fin 5 → Fin 5 → Sign`. Define plus/minus parts as integer-valued matrices and B by the literal transpose/subtraction formula; prove support equals `A i j = plus ∨ A j i = minus`. Define irreducibility first by absence of a nonempty proper block cut (or ordinary permutation-block reducibility), prove its equivalence to strong connectivity on support, and prove a no-outgoing-cut obstruction. This avoids silently redefining the source term.

Use the bidirected five-vertex path to prove A and B strong connectivity, finite witnesses for plus rows/columns, and a finite case split on all 25 cells. For nonzero cells, use the six plus witnesses or four cuts in the table. Prove diagonal zero, support cardinal ten and 10>8. If minimality is instead encoded as no proper AP subpattern, prove AP support/plus monotonicity so any proper subpattern sits below a failed one-entry deletion. The final declaration should literally negate `∀ (n : ℕ) (A : Fin n → Fin n → Sign), ZeroDiagonal A → MinimallyAPIrreducible A → nonzeros A ≤ 2*n-2`, with n=5 supplied. No assertion about AP eigenvalues is needed; no abstract certificate predicate should replace the actual source definition. Kernel-checked finite `decide` or explicit case proofs are feasible without native_decide/sorry/admit/axiom/unsafe. This is a plan, not a completed certificate or replay.

## Integrity and failures

Scientific originals were frozen before reading. `freeze.json` lists fixed original/copy hashes; all pairs were compared before and after the source/extraction phase and are rechecked by the separate final verification. The snapshot uses a bounded shallow set of the assigned scout's files and its immediate diagnostics, without copying historical evidence trees. It includes unrelated shallow scout files for integrity but does not purport to review their science. Administrative files are snapshots only.

Worker failures retained include `diagnostics/runs/milp6.err`: std::bad_alloc after 156.64 seconds, peak sampled group RSS321220608, and no n6 optimum; the source notes earlier locale/thread allocation and graph-merge failures. Worker administrative deviations record unguarded import checks, an intcay text edit, and a no-op. This reviewer used the mandated helper for Python, retrieval, extraction, rendering, copying and hashing, with OPENBLAS_NUM_THREADS=1, OMP_NUM_THREADS=1, PYTHONDONTWRITEBYTECODE=1 and unchanged AS/groupRSS512MiB, CPU210, wall230 caps. Native bounded reads and apply_patch were used as permitted. Publisher PDF extraction/render failure and citation429 are additional preserved failures, not silent clearance.

`manifest.json` excludes itself and `receipt.json`. After final writes, `verify.py` is run separately through the guard to check manifest coverage, every frozen original/copy pair, all new response pairs, and rerun the independent checker without importing any worker module. `receipt.json` reports the outcome. Acceptance and all shared/count changes remain exclusively with root.
