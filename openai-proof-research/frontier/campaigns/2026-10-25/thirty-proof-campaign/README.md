# Thirty verified MathDB source-question outcomes

Completed: **30/30 distinct source questions**. Each package has a complete Lean proof of its expressly claimed mathematical outcome, a written paper and inspected PDF, source provenance, independent review, and a successful rebuild from extracted archive sources. Lean4.34.1 and pinned mathlib dependencies are used; the transitive audit permits only standard logical axioms. No supporting lemma, numerical instance or equivalent corollary adds a count.

The [original twenty](../twenty-proof-campaign/README.md) and their releases are preserved byte for byte. The extension used standard/default speed only and included Pi `spark/GLM-5.3-Flash-EXL3` for broad discovery; its subtraction-Nim and Rust candidates were carried through full formal verification. Native agents independently authored and reviewed further results in parallel.

These are **not thirty claims of new discovery or unqualified solutions of open problems**. Known-result formalizations, counterexamples and clearly labeled corrections are included. In particular,334772 is a literal corpus correction under a solution-count interpretation (the cited manuscript does not state it);371202 proves the explicit square-uniform model, while the source leaves sampling unspecified;336624 corrects printed signs and does not refute a sign-corrected classification;376980 concerns the literal formulation without strictness. Every package preserves its precise scope and prior mathematical credit.

## Ten additional outcomes

| Outcome | MathDB | Claimed outcome | Artifacts |
|---|---|---|---|
| 21 | [334772](https://mathdb.com/p/334772) | Unrestricted additive-count monotonicity (literal corpus statement) | [paper](outcomes/additive-monotonicity/build/main.pdf) / [certificate](outcomes/additive-monotonicity/README.md) |
| 22 | [372496](https://mathdb.com/p/372496) | Higher-power eigenvalue weak majorization | [paper](outcomes/weak-majorization/build/main.pdf) / [certificate](outcomes/weak-majorization/README.md) |
| 23 | [380287](https://mathdb.com/p/380287) | Three-matrix coefficient-minor stability | [paper](outcomes/coefficient-minor/build/main.pdf) / [certificate](outcomes/coefficient-minor/README.md) |
| 24 | [371202](https://mathdb.com/p/371202) | Square-uniform Fibonacci minimum probability | [paper](outcomes/fibonacci-minima/build/main.pdf) / [certificate](outcomes/fibonacci-minima/README.md) |
| 25 | [336624](https://mathdb.com/p/336624) | Sign correction for the nonreducible n-ary classification | [paper](outcomes/ternary-sign/build/main.pdf) / [certificate](outcomes/ternary-sign/README.md) |
| 26 | [376980](https://mathdb.com/p/376980) | Minimum means counterexample to unrestricted both-types classification | [paper](outcomes/invariant-minimum/build/main.pdf) / [certificate](outcomes/invariant-minimum/README.md) |
| 27 | [358595](https://mathdb.com/p/358595) | Ordinary versus symplectic quadratic differences | [paper](outcomes/quadratic-difference/build/main.pdf) / [certificate](outcomes/quadratic-difference/README.md) |
| 28 | [381863](https://mathdb.com/p/381863) | Insufficiency of Pfaffian invariants for symplectic congruence | [paper](outcomes/symplectic-orbits/build/main.pdf) / [certificate](outcomes/symplectic-orbits/README.md) |
| 29 | [374728](https://mathdb.com/p/374728) | A nonvacuous reverse-mex characterization counterexample | [paper](outcomes/reverse-mex/build/main.pdf) / [certificate](outcomes/reverse-mex/README.md) |
| 30 | [356369](https://mathdb.com/p/356369) | Rust's Tribonacci game-sequence identity | [paper](outcomes/rust/build/main.pdf) / [certificate](outcomes/rust/README.md) |

The [ledger](ledger.json) contains all thirty records, exact package hashes, scope and existing-result labels. [archive-replays.json](archive-replays.json) preserves the ten new extracted-source replay receipts. [collection-verification.json](collection-verification.json) binds the final aggregate and each nested package. The independent [infrastructure review](reviews/collection-infrastructure-review.md) and all mathematical reviews are retained under reviews/.

The release is `openai-proof-research/output/release/thirty-proofs-v1.zip`; it contains thirty self-contained nested packages, including the untouched original twenty. Extract the desired nested archive and follow its README. The aggregate checksum manifest and collection manifest verify every byte. Third-party full source snapshots remain in separate local research lanes, with primary URLs and content hashes supplied in the distributable packets.

To reproduce one extension proof from the campaign, run `python3 verify_outcome.py outcomes/<name>`. To rebuild the aggregate from accepted artifacts, run `python3 collect_release.py`. The latter rejects an incomplete/duplicate tally, altered original acceptance anchor, missing review/replay evidence, noncanonical archive paths, or mismatched source/PDF bytes.
