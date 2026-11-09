# MathDB 335230 — independent source, mathematical and Lean fidelity review

2026-11-01 UTC. **Four fidelity gates PASS, under the stated prebuilt-cache trust boundary. Overall acceptance HOLD; current credit 0.** This is one universal-conjecture refutation, conditionally eligible for at most one result. It does not change the campaign's accepted 1/20. The separate significance review's ordinary/source PASS, qualified significance PASS and material Xu-2016-thesis-body HOLD are retained. This review gives no novelty clearance and no acceptance credit. Paper and root final acceptance remain later work.

## Method and integrity

Read the applicable AGENTS.md in openai-proof-research, new-discoveries-batch2 and new-twenty-2026-10-31, checking ancestors through filesystem root; read upstream.json, the manuscript catalogue context and inherited campaign context. No child, git operation, shared edit, external message, publication, upload, browser tab or fresh retrieval was used. All writes are inside this assigned directory. The frozen candidate was neither repaired nor modified.

All 29 absolute file bindings matched before inspection and after all testing; see integrity-before.json and integrity-after.json. All 21 entries of the candidate artifact-hashes.json also matched. The three primary PDFs match both frozen SHA-256 bindings and HTTP receipt lengths. Re-extracted text was generated independently from the actual PDF bytes, rather than trusting the author's text summaries. The original corpus chunk hash and exact line 4667 hash were checked, and its parsed object equals literal record 335230; see literal-check.json. These integrity claims concern the specified inputs, not every file in the shared workspace.

Read fresh-corpus-r15/PROOF.md and the full 130-line Lean source, all packet metadata and replay script, literal statement/provenance, source receipts and source version metadata. The author's eleven endpoint audits and root replay were not used as independent verification. After independently checking the claim, read the frozen significance REVIEW.md to retain its separate dispositions.

## Gate 1 — literal source scope and versions: PASS

Literal record 335230 quantifies over positive integers M,A,K. It asserts D(K_A^(M),K) = (ceil(M/K)-1)A. The cached primary bodies inspected are:

| Primary body | Retrieval receipt UTC | SHA-256 | Target |
|---|---|---|---|
| arxiv.org/pdf/1702.01442v2, dated 7 Nov 2019 | 2026-11-01 07:06:13 | 9c425221658928e34a8d4417a5ba1d6e1ec8452d0b4866a7e47ba7c4e85b6359 | Section 2, equation (1), Section 3.3, Conjecture 2, p.8 |
| arxiv.org/pdf/1702.01442v1, dated 5 Feb 2017 | 2026-11-01 07:06:53 | ebbdfcf81a41941068a5defd7ff100bc5eb5960a0f0d981ffceed46ce2b92a32 | Same definitions and Conjecture 2, p.8 |
| people.computing.clemson.edu/~goddard/papers/fractionalDefectPreprint.pdf, undated | 2026-11-01 07:10:08 | 35a118477c98f228ba5be952be8684b5baca4999662008f65916fa3031d559cd | Section 2, equation (1), Section 3.3, Conjecture 1, p.8 |

Independently read equation (1), the feasible-set and minimum paragraphs, composition definitions, conjecture context and relevant Section 3.3 proofs in all three bodies. Usages are independently assigned nonnegative real numbers summing to one at each vertex. Overlap sums coordinatewise minima, vertex defect sums over neighbors, and graph defect is the maximum over vertices. No constancy of usages within parts is imposed. Replication is an upper-bound construction, not a constraint. The conjecture explicitly uses K colors; the subsequent separate two-color theorem does not restrict it to K=2. The divisible-case theorem does not apply at M=4,K=3.

The author preprint has different numbering and a differently organized two-color argument; it is not authenticated as a version of record. The cached arXiv landing page lists v1/v2 and no identified journal reference. No separate journal body is known to exist here, and its hypothetical absence is not a fabricated requirement. Source fidelity PASS is specifically to these three inspected versions and the frozen literal corpus record, not a live MathDB status claim.

Separate limits: Xu's 2016 dissertation is a material direct predecessor. Official full-body access and the separate review's landing-page access returned 403; this review did not retry either route. Palomar and MathDB 403 gaps remain. The thesis body was not inspected and is not cleared. That is a separate literature/subsumption HOLD, not a defect in the inspected conjecture's statement mapping.

## Gate 2 — mathematical and formal correspondence: PASS

| Source component | Exact Lean representation and assessment |
|---|---|
| M independent parts of size A | Vertex m a = Fin(m+1) × Fin(a+1); M=m+1, A=a+1 |
| All and only cross-part edges | Adj v w means v.1 ≠ w.1; symmetric, irreflexive, and independent of second coordinates |
| K real usages per vertex | Coloring m a k = Vertex m a → Fin(k+1) → ℝ; K=k+1 |
| Per-vertex simplex | Valid is coordinate nonnegativity and sum equal to one, independently at every vertex; upper bound one follows |
| Equation (1) | defect sums all vertices with zero on nonedges, and sums min(f v c,f w c) on edges |
| Maximum vertex defect | graphDefect is Finset.univ.sup' over the nonempty finite vertex type |
| Claimed minimum | MinimumDefect is IsLeast of exactly the attainable valid graph-defect values |
| Numerical invariant | D is real sInf of that same set; D_eq_of_minimum identifies any attained source minimum with the infimum |
| Ceiling prediction | predicted = (real cast of natural quotient (m+1+k)/(k+1), minus real 1) times (a+1) |
| Universal statement | SourceConjecture and NumericalSourceConjecture quantify over all natural indices, hence cover every positive source triple |

For positive M,K, integer division (M+K-1)/K is exactly ceil(M/K): writing M=qK+r, r=0 yields q and 0<r<K yields q+1. This is an independent semantic check of the encoding, not a claim that a generic real-ceiling bridge theorem occurs in the packet. Subtraction is in ℝ after the cast. Since M>0, the quotient is at least one. No zero-parameter, empty vertex set, empty color set, extra symmetry assumption or hidden hypothesis creates the refutation. Even the literal minimum endpoint alone suffices, without relying on the global numerical encoding.

The infimum argument is legitimate: defect_nonneg and graphDefect_nonneg prove the attainable set is bounded below by zero. D_witness_le explicitly supplies the valid witness as a member and applies csInf_le to that bounded-below set. General nonemptiness also follows independently by assigning color zero with usage one everywhere. The source's general minimum-attainment argument is continuity on a finite product of closed bounded simplexes. A generic Lean compactness/attainment theorem is not included, but is unnecessary for this refutation: IsLeast at value 2 entails every feasible objective is at least 2, directly contradicted by the witness. D_eq_of_minimum and the bounded nonempty infimum proof additionally certify the numerical formulation without needing an optimizer.

Independent exact Fraction arithmetic, in independent-arithmetic.py/json, reconstructs the full 8×8 cross-part overlap matrix. With vertex order A0,A1,B0,B1,C0,C1,D0,D1 the defects are (2/3,2/3,5/3,5/3,5/3,5/3,5/3,1). For example C0 receives 2/3 from each B and 1/3 from D0; C1 receives 2/3 from D0 and 1 from D1. Every within-part contribution is excluded. All vectors sum to one and are nonnegative. Thus this coloring's maximum is exactly 5/3, while the conjecture predicts 2. The Lean witness has precisely these vectors at indices (3,1,2), representing actual (4,2,3).

Endpoints checked: witness_valid; witness_defects (an upper bound, despite its name); graphDefect_witness_le; D_eq_of_minimum; defect_nonneg; graphDefect_nonneg; D_witness_le; D_strict_counterexample; literal_minimum_refuted; source_conjecture_false; numerical_source_conjecture_false. Both universal negations specialize at (3,1,2). No theorem equates the unknown optimum to 5/3.

## Gate 3 — fresh strict rebuild and complete local axiom audit: PASS

Safe extraction into this review's new fresh/ directory rejected absolute paths, parent traversal, backslashes, duplicate members and symlinks, and bounded member sizes. Seven regular files were extracted. extraction.json records every member hash. The extracted Lean and PROOF.md match their frozen originals byte for byte; the packet's literal JSON equals record 335230. All nine manifest package revisions were matched against installed repository metadata without git commands; dependency-revisions.json records them. This establishes metadata alignment, not that dependency sources were clean or rebuilt.

Ran the unmodified extracted replay.py with a sanitized env -i environment. It rebuilt the exact extracted source with Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52, using -DwarningAsError=true -j 1 -M 2048, 8 GiB address space, soft CPU limit 90 seconds (packet hard limit 95), and 105-second wall timeout. Exit 0, 4.085412 seconds, maximum child RSS 1,914,752 KiB. See fresh/replay-result.json and fresh/replay.log. Source SHA-256 is 7edeb2e5f485f6ed059d1d01722f0881e451d0eaa9c7bab8d275d72c6f4353f3. No old local olean was imported as the candidate. The fresh module was elaborated and kernel checked.

A separate AuditAll.lean is the identical source plus a review-only command enumerating ALL current-module declarations, regardless of name. It rejects local unsafe declarations, local axiom declarations and any collected axiom outside the whitelist. It checked 32 declarations, including generated equations, anonymous Decidable instance helpers and witness/maximum proof helpers, rather than merely the eleven named theorems. Every declaration's Lean.collectAxioms result is recorded in audit-all.log/declaration-audit.json. Only propext, Classical.choice and Quot.sound occur. This independent run also used strict warnings, -j1/-M2048, sanitized environment, 8 GiB, bounded CPU/wall time and explicit two-CPU affinity; exit 0 in 4.364899 seconds, RSS 1,919,692 KiB. No source sorry/admit/custom axiom/unsafe/native_decide/ofReduceBool was found; source-scan.json records the lexical screen in addition to the compiled audit. No prohibited facility is hidden in a local unexamined declaration.

Trust boundary: prebuilt mathlib and dependency oleans are external trusted inputs. No full upstream source rebuild, dependency cleanliness audit or source-to-olean provenance has been established. Lean 4.34.1 collectAxioms traverses current-module bodies and uses exported axiom summaries for imported declarations (inspected Lean/Util/CollectAxioms.lean); those cached summaries are inside this trust boundary too. Cache hashes or matching revision metadata cannot remove it. No claim that every imported tactic implementation is safe or independently verified is made. Installed caches and old files were preserved. Optional leanchecker was not used.

## Gate 4 — reproducibility and claims scope: PASS

The seven-file packet provides the exact source, replay script, dependency pins/manifest, literal record, proof and dated source receipts. It reproduces under the available pinned prebuilt-cache environment. External PDFs are authenticated against local frozen receipt hashes; they are not bundled in the zip, and no offline self-contained upstream rebuild is claimed. replay.py assumes an existing dependency cache and does not itself authenticate it. This review independently verified the local package revision metadata and source bindings. The packet's source-receipts.json predates the last thesis-403 entry of the outer source log; it is not a complete access-failure history. PROOF.md and the outer frozen log do preserve the thesis gap, so this omission does not falsely clear it.

The certified outcome is D(K_2^(4),3) ≤ 5/3 < 2, hence failure of the universal predicted equality. It does not establish optimality, D=5/3, smallest counterexample size, a classification, new credits for scaling or parameter variants, or exhaustive search. The exact maximum 5/3 is for the exhibited coloring only. Paper review is outside this technical packet gate and remains pending. No acceptance is implied by a successful kernel run.

## Objections and handoff

No actionable mathematical/source/Lean fidelity failure was found in the frozen candidate. The actionable acceptance objection remains the direct Xu2016 thesis-body subsumption HOLD: obtain an independent lawful full copy for comparison, or have the root expressly adjudicate the material unresolved gap. Do not retry denied routes or silently treat a later retained conjecture as proof that the thesis cannot subsume the witness. Version identity remains bounded to the inspected sources; do not require an unknown journal body or claim worldwide priority. Passing this review cannot discharge novelty, the paper gate or root final acceptance. Current credit remains 0.
