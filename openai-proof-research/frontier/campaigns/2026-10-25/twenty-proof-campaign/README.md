# Twenty Lean-verified mathematical outcomes

**Complete: 20/20 distinct MathDB source-question outcomes.**

[Download all twenty packages](../../../../output/release/twenty-proofs-v1.zip). Every package contains its full claimed-outcome Lean proof, paper, provenance, independent review, and reproducibility records. Each released archive passed an extracted-source rebuild and member-hash verification.

These are twenty verified outcomes, not twenty claims of new mathematical discovery. Known-result formalizations, complete counterexamples, and explicitly labeled literal-source corrections are included. The two arithmetic inequalities share a joint paper and proof module but are distinct source questions. Supporting lemmas, dimensions, and the Bernstein monotonicity/minimum corollaries add no counts.

| # | MathDB | Question / outcome | Proof package | PDF |
|---|---|---|---|---|
| 1 | [336488](https://mathdb.com/p/336488) | Diagonalizability conjecture for premagic matrices | [Files](../premagic-diagonalizability/README.md) | [Paper](../../../../output/release/premagic-diagonalizability-v1/paper.pdf) |
| 2 | [336487](https://mathdb.com/p/336487) | Norm-one conjecture for dominant eigenvectors of non-negative premagic matrices | [Files](outcomes/norm-one/README.md) | [Paper](../../../../output/release/twenty-proofs/336487-norm-one-v1/paper.pdf) |
| 3 | [362146](https://mathdb.com/p/362146) | Eigenvalues of permutation-like matrices | [Files](outcomes/permutation-spectrum/README.md) | [Paper](../../../../output/release/twenty-proofs/362146-permutation-spectrum-v1/paper.pdf) |
| 4 | [340783](https://mathdb.com/p/340783) | Fair-discrepancy propagation for fully balanced matrices | [Files](outcomes/fair-discrepancy/README.md) | [Paper](../../../../output/release/twenty-proofs/340783-fair-discrepancy-v1/paper.pdf) |
| 5 | [354537](https://mathdb.com/p/354537) | Scaled Tepper identity | [Files](outcomes/scaled-tepper/README.md) | [Paper](../../../../output/release/twenty-proofs/354537-scaled-tepper-v1/paper.pdf) |
| 6 | [317856](https://mathdb.com/p/317856) | Positive semidefiniteness of monochromatic-box matrices | [Files](outcomes/monochromatic-box/README.md) | [Paper](../../../../output/release/twenty-proofs/317856-monochromatic-box-v1/paper.pdf) |
| 7 | [369281](https://mathdb.com/p/369281) | Nonzero spectrum of the one-shelf position matrix | [Files](outcomes/shuffle-spectrum/README.md) | [Paper](../../../../output/release/twenty-proofs/369281-shuffle-spectrum-v1/paper.pdf) |
| 8 | [366458](https://mathdb.com/p/366458) | Four algebraic properties of signed-set fusion | [Files](outcomes/sigma-fusion/README.md) | [Paper](../../../../output/release/twenty-proofs/366458-sigma-fusion-v1/paper.pdf) |
| 9 | [373182](https://mathdb.com/p/373182) | A continuous nonlinear solution of the Matkowski equation | [Files](outcomes/matkowski/README.md) | [Paper](../../../../output/release/twenty-proofs/373182-matkowski-v1/paper.pdf) |
| 10 | [371201](https://mathdb.com/p/371201) | Weight preservation for Fibonacci recurrences | [Files](outcomes/fibonacci-weight/README.md) | [Paper](../../../../output/release/twenty-proofs/371201-fibonacci-weight-v1/paper.pdf) |
| 11 | [369280](https://mathdb.com/p/369280) | Quadratic eigenvector of the one-shelf position matrix | [Files](outcomes/shuffle-quadratic/README.md) | [Paper](../../../../output/release/twenty-proofs/369280-shuffle-quadratic-v1/paper.pdf) |
| 12 | [349070](https://mathdb.com/p/349070) | Graph-normalization adjacency inequality | [Files](outcomes/graph-normalization/README.md) | [Paper](../../../../output/release/twenty-proofs/349070-graph-normalization-v1/paper.pdf) |
| 13 | [372794](https://mathdb.com/p/372794) | A positive recurrence for the Fill--Janson polynomial | [Files](outcomes/coefficient-positivity/README.md) | [Paper](../../../../output/release/twenty-proofs/372794-coefficient-positivity-v1/paper.pdf) |
| 14 | [350342](https://mathdb.com/p/350342) | Thirty-eight prime outputs refute the Ova counting bound | [Files](outcomes/ova-count/README.md) | [Paper](../../../../output/release/twenty-proofs/350342-ova-count-v1/paper.pdf) |
| 15 | [325243](https://mathdb.com/p/325243) | Endpoint correction for positivity rigidity | [Files](outcomes/positivity-rigidity/README.md) | [Paper](../../../../output/release/twenty-proofs/325243-positivity-rigidity-v1/paper.pdf) |
| 16 | [375256](https://mathdb.com/p/375256) | Arithmetic-function simple ratio inequality | [Files](outcomes/simple-arithmetic/README.md) | [Paper](../../../../output/release/twenty-proofs/375256-simple-arithmetic-v1/paper.pdf) |
| 17 | [375257](https://mathdb.com/p/375257) | Arithmetic-function mixed ratio inequality | [Files](outcomes/mixed-arithmetic/README.md) | [Paper](../../../../output/release/twenty-proofs/375257-mixed-arithmetic-v1/paper.pdf) |
| 18 | [368725](https://mathdb.com/p/368725) | Inactive-coordinate rotations refute permutation rigidity | [Files](outcomes/permutation-rigidity/README.md) | [Paper](../../../../output/release/twenty-proofs/368725-permutation-rigidity-v1/paper.pdf) |
| 19 | [327180](https://mathdb.com/p/327180) | Global convexity of the Bernstein basis square-sum | [Files](outcomes/bernstein-shape/README.md) | [Paper](../../../../output/release/twenty-proofs/327180-bernstein-shape-v1/paper.pdf) |
| 20 | [370245](https://mathdb.com/p/370245) | A rational counterexample to both Schur stability assertions | [Files](outcomes/schur-stability/README.md) | [Paper](../../../../output/release/twenty-proofs/370245-schur-stability-v1/paper.pdf) |

The [ledger](ledger.json) records exact scope, prior-status labels, archive hashes, and review/replay results. The [counting audit](reviews/counting-audit.md) checks duplicate exclusions and the acceptance process. The collection is assembled by `collect_release.py`, which requires twenty accepted records and matching archive/source/replay evidence.

The [historical audit](HISTORICAL-AUDIT.md) is separate: earlier papers retain their written-proof status, but supporting formalizations were not counted as full main-result certificates in this campaign. No external publication or posting was performed.
