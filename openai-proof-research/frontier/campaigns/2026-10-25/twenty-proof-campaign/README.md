# Twenty fully verified mathematical outcomes

Target: **20 distinct source problems** with exact stated outcomes, complete Lean proofs, papers, independent reviews, and reproducible verification.

Current fully verified count: **7/20**. The goal remains active.

| # | MathDB | Outcome | Package |
|---|---|---|---|
| 1 | [336488](https://mathdb.com/p/336488) | Diagonalizability conjecture for premagic matrices | [Files](../premagic-diagonalizability/README.md) |
| 2 | [336487](https://mathdb.com/p/336487) | Norm-one conjecture for dominant eigenvectors of non-negative premagic matrices | [Files](outcomes/norm-one/README.md) |
| 3 | [362146](https://mathdb.com/p/362146) | Eigenvalues of permutation-like matrices | [Files](outcomes/permutation-spectrum/README.md) |
| 4 | [340783](https://mathdb.com/p/340783) | Fair-discrepancy propagation for fully balanced matrices | [Files](outcomes/fair-discrepancy/README.md) |
| 5 | [354537](https://mathdb.com/p/354537) | Scaled Tepper identity | [Files](outcomes/scaled-tepper/README.md) |
| 6 | [317856](https://mathdb.com/p/317856) | Positive semidefiniteness of monochromatic-box matrices | [Files](outcomes/monochromatic-box/README.md) |
| 7 | [369281](https://mathdb.com/p/369281) | Nonzero spectrum of the one-shelf position matrix | [Files](outcomes/shuffle-spectrum/README.md) |

The [historical audit](HISTORICAL-AUDIT.md) found 0/19 full main-theorem Lean certificates among the earlier campaign's accepted papers. Those papers retain their prior written-proof status; they do not meet this campaign's stronger formal-coverage criterion.

We count each source question once, not each lemma, dimension, or normalization. The norm-one result is explicitly an elementary correction to a literal unnormalized statement. The fair-discrepancy counterexample was previously posted by Shivam Patel and is credited; the contribution here is formal verification. No worldwide-priority assertion is made for any result.

See [ledger.json](ledger.json) for exact scope and archive hashes, and [NEXT.md](NEXT.md) for current work. All accepted releases have passed an extracted-source Lean rebuild and full file-hash checks. No new external publication is authorized by this continuation.

The monochromatic-box entry records a theorem already resolved in 2017. The shuffle-spectrum entry corrects the printed index endpoint. Each entry retains its prior-status and scope labels.
