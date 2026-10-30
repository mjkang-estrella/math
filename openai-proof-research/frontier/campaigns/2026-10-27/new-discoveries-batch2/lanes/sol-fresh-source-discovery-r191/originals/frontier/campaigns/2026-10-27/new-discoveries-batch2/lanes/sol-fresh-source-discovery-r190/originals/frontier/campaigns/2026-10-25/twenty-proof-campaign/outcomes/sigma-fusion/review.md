# Independent review: sigma-fusion and Matkowski

Review date: 2026-10-25 (America/Los_Angeles). Scope: the two canonical outcomes in `../outcomes/`, their algebra-lane originals, and archived primary sources in `../../twenty-proof-algebra-lane/sources/`. I read the repository `AGENTS.md`, the relevant source statements, both complete Lean files, both written proofs and TeX manuscripts, and the coverage/source records. This review writes only this file; it does not change proofs, build files, indexes, or Git state.

## Verdicts and counting

| Outcome | Mathematical verdict | Formal coverage | Counting recommendation |
| --- | --- | --- | --- |
| MathDB 366458, sigma-fusion | **PASS for the four explicit algebraic claims of source Conjecture 3.2.** The signed-pair interpretation is an exact presentation of the source's generated signed-subset algebra, not a finite or restricted stand-in. | All four claims for arbitrary ground types; generation/surjectivity, closure, identity uniqueness, annihilator uniqueness, and commutativity are proved. The source's nonstandard foundational theory is not formalized. | One distinct complete algebraic proof outcome. Do not call it a proof that the structure is a loop in the usual sense; do not count related MathDB 318649 again. No worldwide novelty verdict. |
| MathDB 373182, Matkowski | **PASS as a complete formalization of a known counterexample.** | Continuity on all of R, the equation at every real input, and failure of every two-half-line-linear representation are proved together. | One distinct complete proof outcome if known-result formalizations are eligible. **Not a newly solved open problem or a new disproof:** credit Tibor Kiss. |

There are no mathematical blockers in these two certificates. There are minor canonical-package metadata/reproducibility defects below. These two outcomes can supply two distinct proofs, but cannot supply two newly resolved open conjectures. This review makes no determination about the other eighteen outcomes.

## Exact reviewed artifacts and independent verification

Paths in this table are relative to `twenty-proof-campaign/outcomes/`. Hashes are SHA-256 of the actual canonical files, not the lane's earlier TeX.

| Artifact | SHA-256 |
| --- | --- |
| `sigma-fusion/formal/SigmaFusion.lean` | `98fc0e7ab47d95372fee3209b8f2e467dba47cc8fe4bf5d5d8f1d452b91a9580` |
| `sigma-fusion/main.tex` | `2b6d4adbeaddae844656da9f1c4b8b132ae345cf73274f3a370a72231c64b95e` |
| `matkowski/formal/Matkowski.lean` | `9d4d9e3e5cecd75f6c8329c0d5a7d389683947b3f60426164895a15997a438c7` |
| `matkowski/main.tex` | `6d38c435d7d2031ea38f061d4a310abbcf816e2a037e0f52384a3c17c41794d0` |

I independently compiled each canonical Lean source through
`/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean --stdin -DwarningAsError=true`, supplying the file text followed by `#check` and `#print axioms` for **every** locally declared definition/theorem. `LEAN_PATH` contained only the compiled mathlib/dependency library paths under `frontier/campaigns/2026-10-14/formal/.lake/packages`, not either lane's or canonical outcome's local object directory. No `-o` output was requested and no parent build files were written. Thus a stale local `.olean` could not substitute for either reviewed proof.

Results: **exit 0, 25/25 declarations for SigmaFusion; exit 0, 12/12 declarations for Matkowski.** Every axiom report contained only `propext`, `Classical.choice`, and `Quot.sound`. Both files import only `Mathlib`; neither contains `sorry`, `admit`, `native_decide`, or a custom `axiom` declaration. This independently confirms, rather than merely repeats, the existing compiled audits. The recorded environment pins mathlib to `d13f23b723b8a846827a245b89c10fc7d3f11612`; I did not run a Git-based dependency audit, consistent with the no-Git instruction.

The canonical Lean sources, `PROOF.md`, and `coverage.json` are byte-identical to their corresponding lane originals. The canonical TeX differs from lane `paper.tex` in presentation, author line, and formatting of declaration names; the mathematical statements and proofs agree. Current canonical `build/audit.json` and `build/paper-build.json` record the same Lean and TeX hashes listed above. I inspected the TeX argument, not the rendered PDF layout.

## Sigma-fusion: source correspondence and substantive checks

Primary source: Gatica and Bustamante, [*Sigma-Sets and Sigma-Antisets*, arXiv:2501.00047v1](https://arxiv.org/html/2501.00047v1), Definitions 1.2, 1.4, 1.8, 1.12, Theorem 1.6, Section 2/Example 2.1, and Conjecture 3.2. I read the archived HTML, not just the MathDB summary.

**The exact target is the four numbered formulas.** Conjecture 3.2 quantifies over every `A` in the power set of the source's natural numbers, and then over `X,Y` in `3^A`. It asks for closure, a unique two-sided identity, a unique two-sided annihilating inverse for each element, and commutativity. It does not list unique solvability of arbitrary equations `X ⊕ Y = Z`. The four conjuncts of `SigmaFusion.conjecture_3_2` (lines 117–122) have exactly these quantifiers and conclusions after translation of the carrier.

**Why the carrier is faithful.** Definition 1.2 and Section 2 define `3^A` as all fusions of a subset of `A` with a subset of its antiset `A^-`. Index an antielement `a*` by the corresponding `a` in `A`. A signed subset is then represented by its positive and negative index sets `(P,N)`. Theorem 1.6 excludes an element and its antielement coexisting, which is exactly `Disjoint P N` in `Space`. No membership-chain structure inside an atom is used by the fusion formulas.

Definitions 1.4 and 1.8 remove an atom precisely when its opposite occurs in the other operand. Definition 1.12 takes the union of the surviving parts. For `(P,N)` and `(Q,M)` this yields exactly

`((P \ M) ∪ (Q \ N), (N \ Q) ∪ (M \ P))`.

This is the formula in `fusion` (lines 27–35), including a proof that the two output coordinates are disjoint. Closure is consequently not an unproved assumption hidden in a closed result type: the required invariant is proved in the constructor before the final theorem's closure conjunct uses totality.

Fusing a pure positive `P` and a pure negative set indexed by `Q` gives `(P \ Q,Q \ P)`. Every disjoint `(P,N)` is obtained by choosing those same `P,N`; neither loses any elements. `generated_is_fusion`, `generated_covers`, and `generated_space_exact` (lines 48–69) prove these facts internally. This supplies all of the source's generated carrier, including infinite subsets, not just a convenient subspace. Taking the ground type to be `{n : Nat // n ∈ A}` specializes the arbitrary-type theorem to each ordinary set of natural indices. The source identification of its positive/negative natural elements with these indices is a mathematical interpretation explained in the written proof, not a separately formalized theorem about the source's class theory.

**Uniqueness is actually proved.** For `X=(P,N)` and `Y=(Q,M)`, the equation `X ⊕ Y = 0` forces `P ⊆ M`, `Q ⊆ N`, `N ⊆ Q`, and `M ⊆ P`. Hence `Y=(N,P)`. This is the content of `annihilator_eq_inverse` (lines 89–106); `inverse_unique` adds the two-sided witness. Identity uniqueness follows by applying any proposed identity to the empty element. Commutativity exchanges the two terms in each coordinate union. These proofs have no extra finiteness, cancellation, or associativity hypothesis.

**Foundation limitation is legitimate here.** The certificate does not construct or establish consistency of the source's nonstandard sigma-set/class theory, its membership chains, or its annihilation-dimension annotations. A formal theorem about that entire foundational theory would need additional work. Nevertheless, those structures are not required for these four extensional algebraic claims. In particular, Section 2 and Theorem 3.1 explicitly identify the differently annotated empty sets with the same empty set; omitting their annotations does not wrongly collapse distinct elements of the conjectured algebra. On the source's explicit signed-subset semantics, the encoding is exact and the four-part proof is complete. The scope qualification already present in `PROOF.md`, `main.tex`, and `outcome.json` should be retained prominently.

**The usual loop assertion fails for nonempty ground sets.** Idempotence gives `X ⊕ X = X = X ⊕ 0`. Whenever `X ≠ 0`, translation by `X` is not injective, so division is not unique. `translation_not_injective` proves this (lines 139–145). Thus the title “commutative loop conjecture” must not be converted into a conventional loop theorem. Nonassociativity alone would not refute being a loop; the division failure does. `nonassociative_at_nonempty` independently verifies `((-X) ⊕ X) ⊕ X = X` versus `(-X) ⊕ (X ⊕ X) = 0`. The empty ground set is the trivial exceptional carrier and is not covered by the nonempty counterexample premise.

The related MathDB 318649 snapshot states the same four algebraic properties and must remain a duplicate for counting. The archived source still presents Conjecture 3.2, but this review has not independently established literature-wide priority or checked the separate live Qeios revision claimed in the lane notes. Neither is needed to validate the proof; neither should be upgraded into a novelty certification.

## Matkowski: complete counterexample, already in the literature

Primary source: Tibor Kiss, [*A Counterexample to Matkowski's Conjecture for Quasi Graph-Additive Functions*, arXiv:2602.15548v1](https://arxiv.org/html/2602.15548v1), equation (1), the introductory Matkowski conjecture, Proposition 1, and Corollary 1. I checked the archived text of these statements.

The canonical definition `Equation` is exactly

`∀ x : R, f (f (-x) + x) = f (-f x) + f x`.

The witness is `cap x = min (max x 0) 1`. `cap_continuous` uses continuity of min/max on real functions, so it covers the joins at 0 and 1 as well as the open intervals. The proof of `cap_equation` first shows `cap (-cap x)=0`, since `cap x ≥ 0`. If `x ≥ 0`, `cap (-x)=0`. Otherwise `cap (-x) ≤ -x`, so `cap (-x)+x ≤ 0`, and both remaining sides vanish. The Lean case split covers all real inputs, including zero. There is no numerical sampling or omitted branch.

`cap_not_linear_on_positive` uses the exact values `cap 1 = cap 2 = 1`; a positive-half-line slope would satisfy both `b=1` and `2b=1`. `cap_not_two_slopes` therefore rejects **all** real pairs `a,b` in the proposed two-half-line representation. It does not merely rule out slopes satisfying the conjecture's extra bounds or `a ≠ b`. Finally, `continuous_nonlinear_counterexample` bundles the same witness's continuity, all-input equation, and unrestricted nonrepresentation in one existential theorem.

Kiss's Corollary 1 already permits a continuous positive-half-line function between zero and the identity, combined with slope zero on the negative half-line. This capped function is an elementary instance. The source explicitly says that the corollary makes the conjecture false. The MathDB snapshot's `open` status and claim that no resolution is reported conflict with its own cited primary source. The canonical manuscript and proof correctly explain this discrepancy and give credit; retaining the historical database field in `source.json` is acceptable as provenance, not as evidence of current open status. There is no new mathematical disproof here.

## Source records and package findings

For both packages, every field retained in canonical `source.json` exactly matches its corresponding field in the full archived MathDB JSON. These are selected-field extracts, not byte-identical full API snapshots. The full snapshots include empty solution/reply lists. The archived primary HTML hashes match the retrieval manifest:

- `2501.00047v1.html`: `fd9614ca387dd11c3e9b51b9f6bbe07ac2be005869c83fcae4d4df58f023bd7d`.
- `2602.15548v1.html`: `2f869be903a63b0aec3eafdbb0971be0b7b13459cc57ce934790e859d76bedb3`.

**Minor integration finding, both packages:** copied `coverage.json` still names `paper.tex` and `proof.md` and says `pdf_generated: false`, whereas canonical files are `main.tex` and `PROOF.md`, and current canonical builds contain `build/main.pdf`. The README also still points to the lane layout (`formal/rebuild.py`, `formal/build/...`, `../discovery.md`), which is absent from these canonical packages. `PROOF.md` refers to `formal/Checks.lean`, while canonical generated checks currently live under `build/Checks.lean`. These stale paths make the advertised canonical rebuild/navigation instructions misleading. The integrating parent should update the references or clearly link the actual lane rebuild package. This is a documentation/reproducibility defect, not a gap in either mathematical proof or the independent stdin verification.

**Final recommendation:** accept both at the exact scopes above, preserve the sigma-set foundation and conventional-loop qualifications, preserve Kiss's attribution, and repair the stale canonical-package references before presenting them as self-contained deliverables.
