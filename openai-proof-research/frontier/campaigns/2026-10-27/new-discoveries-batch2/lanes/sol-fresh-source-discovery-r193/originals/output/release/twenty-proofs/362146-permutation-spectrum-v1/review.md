# Independent adversarial review: first three candidates

Reviewed 2026-10-25 Pacific / 2026-10-26 UTC. Review applies to the source hashes below, not automatically to subsequent edits, campaign copies, release archives, or rendered PDFs. I read `openai-proof-research/AGENTS.md`, the matrix-lane `discovery.md`, the original statements and source records, all three Lean developments and TeX papers, their type/axiom transcripts, and the rebuild scripts. No agents were used. Only this review file was written; the existing build scripts were inspected but not executed because they write into active build directories.

## Verdicts and counting

| Candidate | Verdict | Exact accepted scope |
|---|---|---|
| MathDB336487, norm-one | **PASS** | Complete counterexample to the literal **unnormalized** eigenvector-norm assertion; elementary normalization correction only. |
| MathDB362146, permutation-spectrum | **PASS** | Full ordinary eigenvalue assertion and zero-eigenvalue criterion in every finite dimension, with a stronger arbitrary-field formal theorem. |
| MathDB340783, fair-discrepancy | **PASS** | Complete verification of **Patel's previously posted counterexample**, for every positive tolerance and every reflexive energy-comparison interpretation. |

No blocking mathematical or formalization gap was found in these versions. These can count as **three distinct question outcomes**, under the user's allowance for elementary corrections and verification of existing counterexamples. They are not three newly discovered research theorems. The 14 + 20 + 30 declaration counts are not additional outcomes. This review neither establishes twenty completed outcomes nor substitutes for the parent's rendered-paper QA and final acceptance.

## Independent compilation and trust boundary

I independently re-elaborated each complete current Lean source through `lean -DwarningAsError=true --stdin`, appending `#check` and `#print axioms` for every local `def`, `theorem`, and `lemma`. `LEAN_PATH` contained only the pinned dependency libraries, not any candidate source directory or candidate build directory. Thus this check did not import a possibly stale local candidate `.olean`. No output-object option was supplied and no build files were written.

All three runs exited 0. All **14**, **20**, and **30** expected declarations respectively produced complete type/axiom inventories; source bytes were unchanged over the runs. Every observed axiom was in `{propext, Classical.choice, Quot.sound}`. There were no `sorryAx` dependencies or extra axioms. The printed main types agreed with the statements analyzed below.

The executable reported Lean **4.34.1**, commit `5045d0056413266e57c625dcd7c365b10e377c52`. I separately checked all nine dependency repositories against `pins.json`: every HEAD matched, and every tracked working tree was clean. Mathlib was `d13f23b723b8a846827a245b89c10fc7d3f11612`.

The saved `audit.json` source hashes match the actual Lean sources. The saved `Checks.log` inventories are complete. For both matrix-lane candidates, every file hash in the receipt (`.lean`, `Checks.lean`, `rebuild.py`, `pins.json`, `lean-toolchain`) also matches. I checked the local matrix source manifest hashes and the norm-one primary-reference PDF/HTML hashes against their retained bodies; they match.

The rebuilders check pins, prohibit proof placeholders, compile before checking the local theorem inventory, and restrict transitive axioms. The norm-one verifier copies the source into its build directory; the matrix scripts compile their source and then check the newly built object with the source directory excluded from `LEAN_PATH`. Their use of existing dependency objects is explicit. My independent stdin check avoids their local-object freshness issue altogether. Neither their receipts nor my run authenticates/rebuilds the compiler or every precompiled dependency object. This is the ordinary declared toolchain trust boundary, not an unproved mathematical hypothesis.

I also read the bounded rational diagnostic program and its receipt. Its 288 finite-function matrices and four discrepancy scales are supplementary checks, not universal proofs. I did not run that script because it writes `independent-checks.json`; the Lean checks above cover the universal assertions directly.

## 1. Norm-one — PASS, literal normalization correction

### Source fidelity

The retained [Teknomo arXiv v2](https://arxiv.org/html/1706.08856v2), Definition 4.3 and Conjecture 7.1, and the MathDB336487 record support the paper's literal target: nonnegative premagic matrix, dominant eigenvector, both norms one. I read the surrounding material, including the discussion of computer simulation and matrix/flow scaling, and checked the corresponding 2019 journal text. There is no stated unit-vector convention governing this conjecture. Matrix normalization elsewhere in the paper does not fix the scale of an eigenvector.

This distinction is substantive. The matrix does admit a unit dominant eigenvector, so the certificate does **not** disprove an existential assertion that one can choose such a vector, a unit-normalized eigensolver output, or an intended convention not present in the text. The TeX paper and `COVERAGE.md` disclose this limitation correctly. Its current normalization caveat must be preserved in summaries and outcome labels.

### Proof and formal coverage

The actual witness is the positive all-ones 2-by-2 matrix and `w = (2,2)`. Every corresponding row and column sum is 2; multiplication gives `Jw = 2w`, and `w` is nonzero. The spectrum proof does not invoke Perron–Frobenius or assume dominance: for a nonzero eigenvector `(a,b)`, the two equations give either `a+b=0` and eigenvalue zero, or `a+b ≠ 0` and eigenvalue 2. This argument works over an arbitrary field, including characteristic two, and its complex specialization bounds the modulus of every eigenvalue by 2.

`NormOneCounterexample.main_counterexample` has **no proof hypotheses**. It combines entrywise positivity, premagic sums, the exhibited nonzero eigenpair, the universal complex eigenvalue bound, and both failures of unit norm. The implication inside the spectral bound merely defines what is to be checked for an arbitrary eigenpair; it is not a dominance assumption supplied to the main theorem.

`w` has mathlib type `EuclideanSpace ℝ (Fin 2)`, and `norm_square` proves its actual Euclidean norm squared is 8. This avoids the common error of using the supremum norm on a plain function type. The separate `frobeniusNorm` is explicitly the square root of the sum of squared real coordinates, the correct Frobenius norm of the column vector. Its failure to equal 1 is proved independently. The TeX proof is sound; its additional general rescaling discussion need not be formalized to certify this finite counterexample.

### Scope and novelty

This is a routine correction of an omitted normalization, not a substantial new spectral theorem. It is distinct from diagonalizability/MathDB336488: this very witness is diagonalizable. It should count once only under the allowed exact-problem-outcome standard. No first-in-literature or first-formalization priority was established.

Reviewed files, relative to `frontier/campaigns/2026-10-25/`:

- `twenty-proof-campaign/outcomes/norm-one/formal/NormOne.lean` — SHA-256 `586b1c47df7bed7306a7823c4e075d66fb5af9016b801b3871fc5dd5bfa8120b`
- `twenty-proof-campaign/outcomes/norm-one/main.tex` — SHA-256 `32c34906f56af2615c38dafdbd04e91d98fa767f42458316558306686628cc9a`

## 2. Permutation-spectrum — PASS, full conjecture

### Source fidelity

I checked [Lippold arXiv v1](https://arxiv.org/html/2403.02478v1), Definition 2.1, Proposition 2.1, the stated results in Section 4.2, and Conjecture 5.2, against MathDB362146. The defining condition really is one 1 per column with all other entries zero, not one per row as well. The original complex-eigenvalue assertion is covered by specializing the arbitrary field to `ℂ` and the finite index type to `Fin d`; no dimension restriction remains to be proved.

The primary source's wording about a permutation matrix “or” the identity is awkward, but its own subsequent note and Corollary 4.7 identify the identity as a permutation matrix. The MathDB wording is the natural redundant exclusion of both. The certificate proves the unambiguous criterion `zero eigenvalue ↔ not a permutation matrix`, then proves the version with the extra `A ≠ 1` conjunct. It does not exploit the wording to prove a weaker claim.

### Proof and formal coverage

`representation` constructs the column map `f`; `transition_mul` proves composition agrees with multiplication; `transition_pow` proves the correspondence for every power. `powers_repeat` uses finiteness of the actual function space to obtain two equal powers with strictly increasing exponents. Eventual periodicity is a proved conclusion, not a premise.

For an arbitrary nonzero eigenvector, `eigenvector_power` establishes the scalar power equation. A nonzero coordinate permits cancellation to get equal scalar powers. After splitting off eigenvalue zero, the difference of exponents is strictly positive and division yields a root of unity. The eigenvector nonzeroness and positivity of the exponent are both present in the checked types.

For zero, a collision of `f` gives the genuine nonzero vector `e_i-e_j`, which works even in characteristic two. Injectivity on the finite set gives a bijection and a constructed left inverse for its matrix. `transition_permutation_iff_injective` proves the row condition rather than assuming it. The paper's parallel handwritten argument is complete.

Most importantly, `isEigenvalue_iff_library` proves equivalence of the local nonzero-vector predicate with mathlib's `Module.End.HasEigenvalue A.toLin' μ`. `exact_mathdb_conclusion` uses that library predicate and assumes only `IsPermutationLike A` plus the stated field/finite-type instances. There is no hidden assumed spectral theorem, restricted class of eigenvectors, or conditional kernel lemma standing in for the main conclusion. The empty-index extension is harmless; the requested `d>1` case is included.

### Scope and novelty

The source already proves the zero-eigenvalue/invertibility part, and the low-dimensional and pre-row spectral cases. The candidate gives appropriate credit. The full finite-map argument is elementary. I did not establish worldwide priority or independently reproduce an exhaustive literature/duplicate search; the discovery record's bounded searches support only their stated limited claims. Count this question once, not once for each spectral part or each field specialization. Jordan forms, multiplicities, and a complete list of which roots occur are not claimed or needed.

Reviewed files, relative to `frontier/campaigns/2026-10-25/`:

- `twenty-proof-matrix-lane/permutation-spectrum-362146/formal/PermutationSpectrum.lean` — SHA-256 `04a5b09a137b126912485aa6732b348225c6ffa0cf594e419fe4444cbee217b0`
- `twenty-proof-matrix-lane/permutation-spectrum-362146/paper/main.tex` — SHA-256 `1388e1911ba113d8f2adb38f56ed3657b13ce27669f6edc16c3afe788fb638ce`

## 3. Fair-discrepancy — PASS, with explicit semantic and attribution boundaries

### Source fidelity and the actual ambiguity

I read [Agama–Kibiti arXiv v3](https://arxiv.org/html/1810.07542v3), Definition 3.1, Example 3.2, Definition 6.2, Conjecture 6.6 and Remark 6.7, in the retained HTML/PDF text, together with the full MathDB340783 record. Approximate equality of row/column energies is not assigned a quantitative definition there. There are also index inconsistencies, including the vertical-balance bound and the rectangular dimensions in Definition 6.2. These are real source deficiencies, not something Lean can silently resolve.

Nevertheless the source explicitly accepts identity/all-ones examples whose energies are exactly equal. Its prose says fairness of a row propagates to other rows. The candidate uses a square matrix, quantifies over **every** entry of the initial row, and adopts precisely that prose interpretation. It therefore does not benefit from the index typos or from weakening the initial-row requirement.

`ExactBalanced` does not purport to be a uniquely canonical definition of the undefined approximate relation. `BalancedWithin` proves the result for every positive absolute energy tolerance, and `BalancedBy R` exposes the relation with a reflexivity hypothesis. That hypothesis is a transparent semantic condition on what approximation means, not an assumed mathematical propagation failure. Exact equality satisfies any such comparison. This is a defensible resolution of the source ambiguity, supported by its own examples. No result for a comparison that rejects equal energies, or for additional unstated normalization/size constraints, is certified.

The source also has a problematic separate unbounded definition of “unfair.” The candidate correctly claims **failure of the strict ε-fair inequalities**, not that stronger unrelated unbounded property. Preserve that wording.

### Proof and formal coverage

For the matrix with rows `(5,5,5)`, `(1,5,7)`, `(7,5,1)`, direct recomputation gives all three row and all three column squared energies equal to 75. Entries are strictly positive. The first row has zero deviations. The second has mean `13/3`, and its first deviation is `10/3`.

For each prescribed `ε>0`, taking `B=εA` gives energy `75ε²`, an ε-fair first row, and second-row deviation `10ε/3>ε`. Thus even an arbitrarily small prescribed tolerance is addressed. The quantifiers are `∀ ε>0, ∃ B`; they do **not** assert that one fixed matrix fails for every arbitrarily large ε. The paper uses the correct order.

The main finite witness, `not_universal_propagation`, `every_tolerance_counterexample`, `every_tolerance_and_balance_counterexample`, and `every_reflexive_interpretation_counterexample` all checked successfully. Nonzeroness, positivity, exact energy identities, means, scaling and failure of fairness are proved, not supplied as assumptions. The final type assumes only reflexivity of the supplied comparison and positivity of ε. It exhibits a positive 3-by-3 matrix with the required balance and failure. It is a full counterexample certificate under the disclosed interpretations, not merely a check of numerical energies.

### Attribution and novelty

The retained API response contains the same matrix **and scaling argument** under Shivam Patel's reply `be21f974-e069-4a4c-b446-252e228a1119`, timestamp `2026-08-22T07:49:47.568226Z`. The TeX paper and README credit both. The API's automated “unverified” status is metadata, not a gap in the now directly checked proof. This work supplies formal verification and explicit interpretation of approximate balance; it must not be marketed as discovering the counterexample or a new disproof. It is one independently checked outcome for a different MathDB question, if existing-result formalization is within the campaign's accepted scope.

Reviewed files, relative to `frontier/campaigns/2026-10-25/`:

- `twenty-proof-matrix-lane/fair-discrepancy-340783/formal/Discrepancy.lean` — SHA-256 `b77c47edc60d5e65e26abc409d36369451281b842749c81eb13a43c9df7c4925`
- `twenty-proof-matrix-lane/fair-discrepancy-340783/paper/main.tex` — SHA-256 `8ea3cd69b98c86333e72eec873829e347922b3eaa2019815e18e2294aa97ffae`

## Integration conditions

No corrective mathematical edit is required for these hashed versions. Preserve the normalization, approximation and existing-counterexample qualifications when integrating the papers. Keep the conjecture IDs separate from declaration counts. Check any changed Lean source again, and compare revised paper claims with the certified types. The two matrix-lane TeX sources reviewed here are the requested neighboring originals; this report does not automatically certify separately edited copies under `twenty-proof-campaign/outcomes/`. Rendered-paper layout and publication/package contents remain the parent's separate work.
