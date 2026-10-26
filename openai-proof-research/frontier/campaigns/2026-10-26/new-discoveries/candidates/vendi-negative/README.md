# Arbitrary-rank negative-order Vendi–LCR comparison

This packet proves the remaining uniform negative-order comparison in Nguyen et al. arXiv:2511.03849v4 / MathDB371345–371346. For every nonempty finite real symmetric PSD matrix Z with diagonal1 and entries in [0,1], VSq≥Dq for every real q<0 without a full-rank assumption, using the positive-spectrum support convention evidenced in source AppendixC.3. The directly defined canonical minus-infinity endpoint is also proved. The two MathDB formulations, finite orders and endpoint form one outcome.

The stronger intermediate bound is Σpositive λj^q ≥ Σi((Z²)ii)^(q−1) ≥ Σi(rowSum_i)^(q−1), for q<1. It follows from classical weighted Jensen with weights λj vj(i)². Known nonnegative-order and full-rank comparisons and the classical Jensen/Hölder–McCarthy ingredient receive no discovery credit. The packet has three frozen Lean modules,48 declarations, a three-page complete paper, independent source/math/formal review, a separate independent manuscript review, source URLs/hashes, dependency pins, all-declaration receipts and rendered-page QA.

## Replay

With Lean4.34.1 and the exact compiled dependencies in verification/pins.json, run from the extracted packet root:

```sh
python3 verification/verify_candidate.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages
```

The verifier checks revisions and tracked cleanliness, compiles isolated byte-identical sources with warnings as errors, and inspects all declaration types/axioms. Only propext, Classical.choice and Quot.sound are allowed; no proof holes, added axioms, unsafe or native_decide are used.

source_conjecture_negative starts from an actual source matrix, with no supplied spectral coupling or invertibility assumption. source_conjecture_negativeInfinity actually selects the least positive eigenvalue and least row sum. There is no formal analytic theorem about q tending to minus infinity and no formal weighted-p matrix bridge.

The latest source already proves q≥0 and negative q at full rank. Its published PRE abstract retains the rank restriction; the full journal body required subscription and was not read. A later Bioengineering article broadly asserts the comparison, citing PRE, but supplies no separate singular-negative proof. Both limitations and classical credit remain explicit in NOVELTY.md and the paper. No absolute priority is certified. No external publication, posting, author contact, upload or push occurred.
