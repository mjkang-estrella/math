# Independent adversarial review of MathDB 377831

Recommendation: **HOLD; zero campaign credit.** This is a review, not root acceptance. The counterexample and its exact Lean endpoint survive the mathematical and technical checks. Novelty does not yet clear the campaign standard: two directly relevant published papers must be compared in full. Their existence is a concrete objection to treating the author's arXiv-only screen as sufficient, not evidence that the candidate is already known.

Review date: 2026-11-01 UTC. Recommended mathematical target: `Cover377831.source_refutation : ¬ Cover377831.SourceConjecture` in `Endpoint.lean`, with the definitions in `Defs.lean`. No alteration of the mathematical packet was necessary. All four extracted mathematical source files are byte-identical to the ZIP. The 1,668 files in expanded-corpus-r72 have identical before/after SHA-256 manifests.

## A — Source fidelity: PASS for the specified arXiv v1

I read the supplied complete source text, particularly Definitions 2–3, Theorems 1–3, Propositions 4–5 and Conjectures 1–2. The source PDF hash is `3f1ed01f3573594d4a971b7446b14b2e73e1ef7c74b6fa5826446a4bede3c430`. The literal MathDB JSONL and results entry were also inspected. The dropped exponent is real: S belongs to the square of the index set. The source uses lines fixing two coordinates. A partial operation must be defined on the prescribed pairs and satisfy row and column output uniqueness. A generalized quotient is the weak quotient by a partition; uniformity is an additional condition. Containment allows a smaller quotient support. These meanings match the formal definitions.

A surjective class map encodes exactly nonempty partition blocks, with no size equality. One common map is used for all three coordinates. Fin n labels an arbitrary finite ground set. Setting S to the full square forces totality; finite row and column injectivity then imply quasigroup bijectivity. Consequently the proof is not restricted to order 3 quasigroups: the partition has three classes, but their total size is arbitrary.

The exact strong quotient of a prescribed domain causes no hidden problem: choose that prescribed domain to be the union of the blocks indexed by S; the operation may also be defined elsewhere. The formal domain conjunct expresses precisely this condition. H is wholly inside S times Fin 3 here, since S is full. Positive k versus Lean's inclusion of k=0 is immaterial to this refutation: the witness is k=3. `CoverNumber` uses a natural infimum; the proof establishes existence of covers before its lower-bound argument, so there is no empty-infimum loophole. Source conjecture quantification is universal in k, H and S.

The live arXiv abstract page lists only v1, submitted 27 March 2003. A [2005 Graphs and Combinatorics version](https://link.springer.com/article/10.1007/s00373-005-0614-3) exists, volume 21, pages 365–375. Its body was unavailable under public access. Thus PASS is explicitly for the task's arXiv v1, not a claim of word-for-word journal equivalence.

## B — Independent ordinary mathematics: PASS

`scripts/exact.py` was written independently from the mathematical data in the brief, without calling author search/validation scripts. It enumerates all 17 triples and all 27 lines, checks each score equality, and expands the quadratic form by integer coefficient collection. `exact.json` records the data.

Integer packing weights total 17 and every line sum is at most 2. Dividing by 2 gives the fractional lower bound 17/2. An integer cover must therefore have at least 9 lines. The nine vertical lines cover. An additional independent memoized exact set-cover recursion, branching on a first uncovered triple, returns minimum 9. Neither floating-point LP nor search over bounded class sizes is used for the proof.

For any finite quasigroup and surjective class map, summing the three scores over ordered input pairs uses column bijections for A and row bijections for B. The resulting sum is the quadratic form of T=A+B+C. Exact coefficient collection gives only the term -r0*r1, all other square and mixed coefficients zero. Since both fibers are nonempty, this is strictly negative. On the hypothesized support every summand is zero: contradiction. This covers unequal classes of all finite positive sizes, not a finite sweep. The formal symmetrization instead yields twice the same contradiction, which is equally valid.

Controls: raising the distinguished packing weight makes a line inequality fail; adding the excluded triple (0,0,1) breaks score-zero. The cyclic order-3 square is not supported in H. These are local certificate checks only, not tests of general logical consistency.

One documentation defect: `outputs/cover.json` is an earlier k=2 diagnostic and does not certify the new H. The results entry labels it a small search. Use `exact.json` and the formal theorem for this candidate.

## C — Lean fidelity and technical audit: PASS

Fresh safe extraction checked ZIP paths, symlink modes and member sizes. The source-only packet supplies four mathematical modules and an audit command module. No author olean was reused. Each mathematical module was freshly built with Lean 4.34.1, `-j1 -DwarningAsError=true`; each passed `leanchecker`. The packaged Audit module was also built and checked separately. The mathematical files contain no sorry/admit/axiom/unsafe/partial/native_decide/ofReduceBool tokens after comments are removed. Lean and leanchecker binary hashes match pins.json. Mathlib cache pin is d13f23b723b8a846827a245b89c10fc7d3f11612.

My independent `proof/ReviewAudit.lean` scans declarations by actual module origin, not namespace prefix. It records the full types, body presence using `value? (allowOpaque := true)`, unsafe and partial flags, and collected transitive axioms. All 35 declarations, including generated declarations, have bodies, are safe and nonpartial, and use only propext, Classical.choice and Quot.sound. See `logs/review-audit.log`. The separate audit command modules are review instrumentation; the 35-declaration count is exactly the four mathematical modules, not the imported Lean elaborator.

The finite checks use kernel `decide`, while the unrestricted quasigroup obstruction is a finite-sum argument. `no_total_quotient` quantifies over an arbitrary finite type Q. `no_partial_quotient` explicitly chooses total outputs from the full domain and transfers both cancellation laws and support. The endpoint then instantiates the universal source conjecture at the verified counterexample. No missing theorem translates a bounded feasibility computation into the unrestricted claim.

Sanity.lean proves that the definitions permit the one-element full quotient and the empty operation with empty S and empty H, and checks the support/line cardinalities. Two expected failures reject a proof of False using True.intro and a type-confused attempt to use the refutation as the conjecture. Their scope is elaboration/type checking only.

All expensive child processes used two-CPU affinity, CPU 120 s, wall 140 s and a systemd user scope MemoryMax=6G. The wrapper uses AS 64 GiB because memory-mapped Lean dependencies need more virtual address space; RSS remains constrained by the cgroup. Initial wrapper setup failures (too-small AS, missing lean on PATH, an untyped audit counter) were corrected; none was a mathematical proof failure. Cached upstream oleans are trusted; this is not a full mathlib rebuild or an independent implementation of Lean's kernel.

## D — Prior art and novelty: HOLD

The original Theorem 2 requires a supported nonnegative integer tensor with prescribed product marginals. It is a realization theorem once such a tensor exists, not a theorem that the integer cover condition produces one. Its existing GQQ-without-GUQQ example has a generalized quotient and therefore cannot directly subsume this no-GQQ witness. The standard odd-cycle obstruction to an ordinary Latin square is also insufficient to rule out arbitrary quotient class sizes.

I searched title variants, both authors, GQPQ/S-GQPQ, covering-number language, partial Latin square quotients, outline/amalgamated squares, Rubio thesis terminology in English and Spanish, and later permutation/group approximation work. Search results alone were not treated as proof bodies or open-status evidence. `receipts/final-search.json` preserves a final search response; earlier query families and discoveries are described here. No indexed Rubio thesis resolving this target was identified.

Actual primary bodies checked include:

* [Glebsky–Gordon–Rubio, math/0304065](https://arxiv.org/html/math/0304065), particularly its matrix construction, Lemmas 1–2, and quotient route. It constructs suitable positive matrix marginals from Haar measure and uses realization. Its discussion that the naive three-dimensional permutation-support assertion fails is not a no-generalized-quotient counterexample.
* [Glebsky–Rivera, 0709.1134](https://arxiv.org/html/0709.1134), the main statements and proofs concerning roots and stability in permutations. They do not provide a covering-number characterization for arbitrary triple supports.
* [Smith, Augmented quasigroups and character algebras](https://jdhsmith.math.iastate.edu/math/AQCA.pdf), especially Proposition 5.1 and Theorem 5.3; and [Stevenson–Smith, Character groups of dihedral and generalized quaternion groups](https://jdhsmith.math.iastate.edu/math/CGDGQG.pdf), §§2.2–2.3. Their lifting results start with weighted quasigroup marginal identities. They do not infer those identities from integer cover number. The score calculation supplies a support-specific certificate denying those marginals. These bodies do not make the candidate a routine corollary by themselves.

The decisive unclosed leads are:

1. The 2005 journal body of the original article, DOI 10.1007/s00373-005-0614-3. Springer explicitly offers subscription/purchase access; its PDF route redirects to the abstract page. This does not verify whether either conjecture changed or was resolved there.
2. Glebsky–Rubio, **Partial Latin Squares and Their Generalized Quotients**, Taiwanese Journal of Mathematics 10(5) (2006), 1157–1167, DOI **10.11650/twjm/1500557295**. This distinct later title appears in the author's ORCID and institutional publication report; its DOI/pages were located in bibliographic search. Project Euclid supplied a security-check iframe, not a paper. I do not infer content, duplication, or resolution from its title.
3. Hilton–Wojciechowski's *Amalgamating infinite Latin squares* (2005), and complete bodies of the earlier Hilton/Dugdale material. Search located an author-hosted PDF but retrieval timed out; the CiteSeer route failed. I have read relevant later restatements, not these original full bodies. These are weaker outstanding leads than item 2, but should not be called cleared.

Public-access limits remain binding. No purchase, login, challenge bypass, author contact or upload occurred. A queued direct HTTP request and web-tool request overlapped on the CiteSeer route and the Euclid PDF route; these duplicate requests should have been deduplicated. The former returned 404 directly and 403 through the web tool; the latter returned challenge HTML with status 200. No further request was made to either route after recognizing its denial/challenge. The misleading tjm.pdf filename contains only HTML, as its 1,156-byte receipt makes explicit. No MathDB/Palomar direct retry or Crossref request was made.

Registry checks used only /commits/HEAD for live heads. OpenAI math remains 4eaee87548250b2682affda7d05d947c05554bae. Omega is now cb0794afb598a762af530e1ebed38deee878e52c, different from the brief's last observation. The full recursive root tree is truncated; fresh separate D5 and Problems listings are complete. Path screens found Latin/tableaux/Eulerian/SudoQ topics but no named covering-quotient resolution. This is a bounded lexical screen, not semantic clearance of every proof body or chronology of an unidentified counterpart. Receipts include response hashes and dated statuses.

## E — Campaign significance: HOLD

Conditional on clearing D, this would be a substantive refutation of the exact unrestricted 2003 converse: the witness prevents all finite nonuniform quotient realizations. It is neither an exponent-only correction, a uniform-class result, padding at an empty parameter, nor a helper lemma. Small k does not make a counterexample to a universal conjecture a mere parameter-instance credit. However, a valid Lean refutation does not establish that it is new to the literature. I recommend zero credit and no acceptance until the 2005 and especially 2006 bodies are lawfully obtained and explicitly compared, including their conjecture statements and examples. Root alone adjudicates acceptance.
