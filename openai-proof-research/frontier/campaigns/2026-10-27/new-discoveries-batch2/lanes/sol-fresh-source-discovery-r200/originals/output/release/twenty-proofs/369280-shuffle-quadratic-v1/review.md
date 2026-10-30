# Independent review: recurrence weights and shuffle quadratic

Review date: 2026-10-25. I read `openai-proof-research/AGENTS.md`, the canonical Lean files, `main.tex`, `PROOF.md`, metadata and reproduction instructions, the original source HTML and full MathDB JSON in the two sibling development lanes, and Patel's posted proof. I independently compiled the canonical proofs. Only this review file was written; no nested agents, Git commands, local proof objects, or build-directory writes were used. PDF building and visual inspection remain the parent's responsibility.

## Verdicts and counting

| Canonical outcome | Mathematical and formal verdict | Full-source counting recommendation |
| --- | --- | --- |
| `fibonacci-weight`, MathDB 371201 | **PASS.** The entire weight-preservation assertion is proved for both source recurrences, every positive divisor of every positive modulus, and every downstairs period, including fixed points. The theorem actually permits every integer recurrence coefficient. | **Yes: one distinct full source outcome**, as a formal verification of Patel's existing proof. No mathematical novelty or newly solved open-problem claim. |
| `shuffle-quadratic`, MathDB 369280 | **PASS.** For every integer deck size `n ≥ 3`, the exact source vector is nonzero and is an eigenvector of the exact source position matrix with eigenvalue `1/4`; the eigenspace dimension is at least one. | **Yes: one distinct full source outcome**, as a formal verification of a known result already resolved by Tripathi. No mathematical novelty or newly solved open-problem claim. |

These provide **two distinct complete source-target proof outcomes** if the campaign admits known-result formalizations. They provide **zero new mathematical resolutions of previously open problems**. Helper lemmas and the recurrence's additional coefficient values are not separate counted outcomes. There are no mathematical or formal coverage blockers. The packaging/reproducibility findings below should be repaired before release; in particular the current shuffle PDF receipt does not certify the reviewed TeX hash.

## Exact reviewed artifacts and independent compilation

Paths below are relative to `twenty-proof-campaign/outcomes/`. Hashes are SHA-256 of the canonical files actually reviewed.

| File | SHA-256 |
| --- | --- |
| `fibonacci-weight/formal/FibonacciWeight.lean` | `fb935e62d0ad0c0876e5169590055da74afe71235dd4c529e5b0d8d45f206b62` |
| `fibonacci-weight/main.tex` | `a5d21fec00a6acddf6b6e43ec56f6898d4be904a1af71a214cc12758f529f10b` |
| `shuffle-quadratic/formal/ShuffleQuadratic.lean` | `01e847efe118200e19caa7c921befcbe7689098a937ca80e3d859260dce0f265` |
| `shuffle-quadratic/main.tex` | `99b552a9e3da0010cf102cd6dc0e4a7fc441bbf48058b75f440183e06b1c564f` |

I invoked `/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean -DwarningAsError=true --stdin` separately for each canonical source. The input was the complete source text followed by `#check Namespace.name` and `#print axioms Namespace.name` for every local `abbrev`, `def`, `theorem`, and `lemma`, including noncomputable definitions. The declaration inventory was independently extracted and compared against the returned axiom-report names. No local module import or cached local `.olean` supplied either proof.

`LEAN_PATH` contained only `.lake/build/lib/lean` under the packages `mathlib`, `plausible`, `LeanSearchClient`, `importGraph`, `proofwidgets`, `aesop`, `Qq`, `batteries`, and `Cli` in:

`/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages`.

The compiler identified itself as Lean **4.34.1**, commit `5045d0056413266e57c625dcd7c365b10e377c52`. The campaign pins and that formal project's `lake-manifest.json` agree on mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` and the listed dependency revisions. I did not run a Git-based revision/cleanliness audit, consistently with the explicit no-Git instruction; the independent result is compilation against the supplied dependency artifacts, not an independently established dependency-cleanliness claim.

| Module | Declaration inventory | Result | Axiom audit |
| --- | --- | --- | --- |
| `FibonacciWeight` | **24 = 1 abbrev + 6 defs + 17 theorems; 0 lemmas** | Exit 0; 24/24 checks and axiom reports; empty stderr | `recurrence`, `reduction`, `reduction_surjective`, and `reduction_commutes`: `propext`, `Quot.sound`. All other 20 declarations: `propext`, `Classical.choice`, `Quot.sound`. |
| `ShuffleQuadratic` | **16 = 3 defs + 13 theorems; 0 abbrevs or lemmas** | Exit 0; 16/16 checks and axiom reports; empty stderr | Every declaration: `propext`, `Classical.choice`, `Quot.sound`. |

The full recurrence inventory is `Period`, `periodOf`, `orbitSize`, `period_eq_iff_iterate`, `orbitSize_eq_minimalPeriod`, `weight`, `commute_pow`, `map_sameCycle`, `periodMap`, `periodMap_mk`, `orbit_sum_eq_preimage`, `uniform_fibers`, `preimage_card`, `total_card`, `weight_preservation`, `orbit_maps_onto`, `recurrence`, `reduction`, `reduction_surjective`, `reduction_commutes`, `card_state`, `reduction_fiber_card`, `zero_period_length`, and `fibonacci_weight_preservation`. In particular **`Period` was audited**; the count is 24, not the earlier 23 obtained by omitting the abbreviation.

The full shuffle inventory is `binomial_quadratic`, `binomial_quadratic_extended`, `vEntry`, `positionMatrix`, `quadraticVector`, `reflected_sum`, `quadratic_reflection`, `row_numerator`, `quadratic_mulVec`, `first_entry_positive`, `quadraticVector_ne_zero`, `quadratic_hasEigenvector`, `quarter_hasEigenvalue`, `quarter_eigenspace_dimension`, `positionMatrix_one_based`, and `quadraticVector_one_based`.

Neither file contains admitted proofs, custom axioms, unsafe declarations, or `native_decide`. The changed campaign verifier's inventory regex now includes `abbrev`; its intended inventory agrees with this independently generated one. I did not run that verifier because it writes build files and invokes Git. Existing canonical Lean audit receipts match these Lean hashes and counts, but my verdict rests on the independent stdin compilations.

## Recurrence: exact source scope and substantive proof checks

The primary source is Pudelko, [*Modular Periodicity of Random Initialized Recurrences*, arXiv:2510.24882v2](https://arxiv.org/html/2510.24882v2), **Conjecture 17, equation (19)**, HTML anchor `Thmconjecture17`. I checked the original HTML statement and the introduction's convention that repetitions are reduced and cyclic shifts represent the same period. Conjecture 17 quantifies over a divisor `d` of a composite modulus `m`, a period modulo `d`, and **all** periods modulo `m` reducing to it, with weight length divided by the square of the modulus. The two recurrences are `a[n+2] = a[n] + a[n+1]` and `a[n+2] = a[n] - a[n+1]`. The MathDB 371201 snapshot agrees with this target.

The canonical final theorem has only `m,d : Nat`, `NeZero m`, `NeZero d`, `d ∣ m`, `eps : Int`, and an arbitrary downstairs quotient class as inputs. Thus it covers all positive moduli, not merely composite ones, and specializes to both source recurrences with `eps = 1` and `eps = -1`. No orbit decomposition, period-length equality, fiber size, or weight identity is assumed as an input.

**The periods are actual periods.** `Period T` is the quotient of the whole state type by `Equiv.Perm.SameCycle.setoid T`, not a quotient of the support or a list of nontrivial cycles. `period_eq_iff_iterate` proves that two representatives define the same class exactly when one is a nonnegative iterate of the other. `orbitSize` counts all states in that quotient fiber. `orbitSize_eq_minimalPeriod` identifies this count with `Function.minimalPeriod` using the noduplicated periodic orbit. The finite permutation hypothesis supplies periodicity, so the library's convention of zero minimal period for nonperiodic points cannot introduce a zero-length orbit here. `zero_period_length` independently gives length one for `(0,0)`.

The concrete map is `T_s(a,b) = (b,a + eps*b)` with inverse `(a,b) ↦ (b - eps*a,a)`; both inverse identities are proved in its `Equiv.Perm` constructor. Consecutive states along its iterates are exactly consecutive entries of the scalar recurrence. Equality of a returned consecutive pair forces repetition of the scalar sequence, and a scalar sequence period returns the pair. Hence the least positive scalar period equals the state return time. This last scalar-sequence interpretation is explained correctly in both written proofs; Lean uses the state representation rather than defining a separate scalar-sequence datatype. There is no missing source hypothesis in that interpretation.

**Every lift is counted exactly once.** `periodMap` is constructed with `Quotient.map` from the proved compatibility with same-cycle equivalence. `orbit_maps_onto` lifts a target iterate of an image point to the corresponding source iterate, proving that the image is the entire downstairs orbit. `orbit_sum_eq_preimage` applies the finite fiberwise cardinality identity to the actual quotient projection. The summed set is exactly all source classes mapping to the specified target, without a selected representative or a restricted family of lifts.

**Uniform fibers are proved for the actual reduction.** `reduction` is coordinatewise `ZMod.castHom`, as an additive homomorphism. Its surjectivity and commutation with the recurrence are established explicitly. `uniform_fibers` derives equal fiber sizes from surjectivity of a group homomorphism; `preimage_card` and `total_card` count arbitrary preimages and the full group. The derived concrete theorem `reduction_fiber_card` gives `(m/d)^2` for every target state. The cardinalities of the state spaces are proved to be `m^2` and `d^2`, and denominator nonzeroness is justified. The final normalized identity follows for every downstairs orbit.

The argument in `main.tex` and `PROOF.md` matches this formal chain, including the orbit partition, least-return interpretation, fixed points, and positive-modulus quantifiers. It is not merely a general helper whose recurrence specialization remains unpaid.

**Prior art:** the full MathDB JSON contains Shivam Patel's proof, solution `b64f2547-2755-408d-8ca3-997917a47b33`, posted **2026-08-20T13:09:09.065341Z**. I read its body and the separate archived text: it already gives the inverse-image orbit partition and the `(m/d)^2` fiber count, and even states the higher-dimensional invertible integral-matrix generalization. The canonical integer-`eps` extension is subsumed by that posted generalization, since its companion matrix always has determinant `-1`. Retain the explicit Patel attribution and all no-novelty labels. The package does not purport to formalize the entire higher-dimensional statement or the source's other conjectures.

## Shuffle: exact source kernel, all deck sizes, and multiplicity

The primary source is Clay, [*Guessing Strategies for Shelf-Shuffling Machines*, arXiv:2507.10294v1](https://arxiv.org/html/2507.10294v1). I checked **Theorem 1.1** (`S1.Thmtheorem1`), **Definitions 2.1–2.2**, and **Conjecture 1** (`Thmconjecture1`) in the original HTML. Cards are drawn from the bottom and placed at the top or bottom with equal probability. The source matrix has initial card index in the row and final position in the column:

`M[i,j] = (choose(i-1,j-1) + choose(i-1,n-j)) / 2^i`, for `1 ≤ i,j ≤ n`.

This is exactly the canonical `positionMatrix` after the explicit one-based translation theorem. The formal result concerns `M v`, not a transpose or the kernel for reversed drawing order. The vector translation theorem gives exactly `v[k] = n^2 - 3*n*k + 3*k*(k+1)/2 - 1`. These are the definitions in both `main.tex` and `PROOF.md`.

**Universal proof:** `binomial_quadratic` proves the quadratic binomial moment identity for every natural `r`, including zero, by Pascal induction. `binomial_quadratic_extended` justifies all added zero-support terms. `reflected_sum` proves the finite reindexing, rather than using an unsupported polynomial symmetry. The reflected bracket is exactly

`3*k^2 + 3*(1-n)*k + (n-1)*(n-2)/2`.

`row_numerator` evaluates every row and `quadratic_mulVec` divides by the correct `2^(r+1)`, obtaining `M v = (1/4) • v`. That equality is valid even for the smaller deck sizes, but the eigenvector claim appropriately requires `n ≥ 3`: the first entry is `(n-1)*(n-2) > 0`. `quadraticVector_ne_zero` and `quadratic_hasEigenvector` prove nonzeroness and the genuine mathlib eigenvector predicate for every such `n`.

**Multiplicity:** `quarter_eigenspace_dimension` proves the geometric multiplicity is at least one. This fulfills the source's “multiplicity at least 1”; if interpreted algebraically, a nonzero eigenvector also implies algebraic multiplicity at least one for this finite real matrix. Neither the package nor this review claims an independently formalized exact multiplicity-one theorem or a proof of the source's separate full-spectrum conjecture. An eigenidentity for a possibly zero vector alone would not have sufficed, but that gap is absent here.

Taking the exact established source kernel as the matrix definition is sufficient for this algebraic source problem. The stochastic derivation is not formalized in Lean, and the written proof says so. Direct source comparison establishes the necessary bridge. As an additional independent check, I enumerated all top/bottom coin assignments for `n = 1..10` in memory and recovered precisely this row/column convention.

**Prior art:** Tripathi, [*On the position matrix of single-shelf shuffle and card guessing*, arXiv:2602.07920v1](https://arxiv.org/html/2602.07920v1), **Theorem I** (`Thmbigthm1`), already gives all nonzero eigenvalues and explicit eigenvectors. Its even index `i=2` is available for every `n ≥ 3`; its vector is

`zeta^(2)(k) = (2/3)*(n-1)*(n-2) - 2*(n-2)*(k-1) + (k-1)*(k-2)`.

Expansion gives exactly `v = (3/2) zeta^(2)`. The original HTML also explicitly makes this comparison in its discussion confirming Clay's Conjecture 1. Thus the no-novelty statement is directly source-backed, not inferred only from a title or abstract. The historical MathDB snapshot still says `open`; it is not reliable evidence of current open status. Preserve it as provenance while retaining the package's clear known-result label. No claim about priority of Lean formalizations has been established.

## Source integrity and supplemental checks

The retained fields of each canonical `source.json` match the corresponding full lane MathDB JSON. The full snapshots, rather than only those extracts, were used to check solutions/status and scope. Recomputed source hashes agree with their manifests:

| Archived source | SHA-256 |
| --- | --- |
| Pudelko `arxiv-2510.24882v2.html` | `f138aa851b08726f0a212ea17e7e23569d4dc7fc562b4c8e361aa7a8a0c0e80e` |
| `mathdb-371201.json` | `87d4eb13fce6f5ed736d6ab13135d2d6cae3f501a48c86a7e36cf337e484ade4` |
| Patel `posted-proof-shivam-patel.txt` | `a3d9229869f88068585f07fd28ea6ad568a6289304171f6ed7b8406e3b5f969f` |
| Clay `clay-2507.10294v1.html` | `711998f7ee7147d3074a2eb91e7d5b7561aa59af9055bf42812c0ce1358ce147` |
| Tripathi `tripathi-2602.07920v1.html` | `cea5344b9d012013dcca896e048ae5e3d3f244a22066ee55ee60879797f42e8b` |
| `mathdb-369280.json` | `cb18b5c3fd6aea391aa565da195be5ecc0b37533e2e5a476e4552f02d6615aca` |

Independent in-memory exact-arithmetic checks passed for the shuffle eigenidentity and zero/nonzero boundary for `n = 1..80`, and all coin assignments for `n = 1..10`. Independently enumerated recurrence orbits and reduction fibers passed for all **462** triples with `1 ≤ m ≤ 20`, positive `d ∣ m`, and `-3 ≤ eps ≤ 3`. These are supplementary sanity checks, not substitutes for the universal proofs. I inspected the lane's mutation-check records but did not rerun its build-writing mutation harness; those reported failures are not represented as new independent compilation results.

## Minor documentation and release findings

1. **Stale canonical metadata paths, both outcomes.** Recurrence `outcome.json` has `paper_source: "paper/main.tex"`; shuffle has `paper: "paper/main.tex"`. The canonical files are `main.tex` at the outcome roots. Shuffle additionally names `notes/source-review.md` and `notes/proof-review.md`, which exist in its development lane but not in the canonical outcome. Repair these paths or include the referenced files.
2. **Review-file claim precedes integration.** Recurrence `main.tex` says an independent `review.md` is included, and `PROOF.md` says source records and review are included separately, but neither canonical outcome currently contains `review.md`. This assigned review is in the campaign's `reviews/` directory. The parent must integrate/link it and bind the reviewed hashes before the packages can truthfully advertise included independent reviews. The `candidate` / “awaiting independent review” metadata is also still pending parent integration; it is not a mathematical failure.
3. **Development-lane reproduction artifacts are not all canonical artifacts.** The shuffle manuscript describes exact checks and mutation tests, but their scripts and receipts are in `../shuffle-quadratic-lane/verification/` and its `build/`, not the canonical outcome or the present packaging script's source selection. Give an explicit development-lane pointer or ship the scripts if those checks are advertised as reproducible from the release alone. The universal Lean verification is independently reproducible with the included-on-packaging campaign verifier. The READMEs correctly distinguish the release's copied verifier from the campaign's `../../verify_outcome.py`; its absence before packaging is intentional, not itself a defect.
4. **Current shuffle paper receipt is stale.** At the final receipt check, `shuffle-quadratic/build/paper-build.json` reports `tex_sha256 = 190ecdf01d4228623d728140d497b61d1e1e2e09ab1a9bed6f55a37442512dc8`, whereas the reviewed canonical TeX is `99b552a9e3da0010cf102cd6dc0e4a7fc441bbf48058b75f440183e06b1c564f`. Its exit-zero receipt cannot certify this TeX. Rebuild/render and regenerate the receipt for the current file before packaging. The recurrence paper receipt does match the reviewed TeX hash. I did not rebuild or visually inspect either PDF.
5. **Historical source metadata discrepancies are not novelty evidence.** The recurrence MathDB extract names the paper as a 2026 source although the cited version is dated 2025; the manuscript correctly cites v2, 3 November 2025. The shuffle snapshot's title differs slightly from the original paper title and its status is stale. Keep extracts recognizable as historical source records, not authoritative updated bibliography or resolution status.

**Final acceptance recommendation:** accept both mathematical/formal outcomes at the scopes above, preserve Patel and Tripathi attribution and every no-novelty qualification, fix the release-path/review integration issues, and require the parent's current-hash PDF build/render confirmation before final release certification.
