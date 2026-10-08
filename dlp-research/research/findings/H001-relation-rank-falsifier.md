# H001.1: low polynomial rank does not give low relation-predicate rank

Verdict: reproduced finite negative result for a proposed shortcut; no ECDLP
improvement. Sol proposed/implemented, coordinator inspected and reproduced,
Astra independently supplied the general obstruction below. No Lean additions.
This is not a solver benchmark, asymptotic fit or rejection of coordinate attacks.

## Hypothesis and decisive observation

For a fixed target x-coordinate z on y²=x³+ax+b, the third Semaev polynomial
can be written `(1,x,x²) C(z) (1,y,y²)^T`. Consequently its evaluation matrix
has rank at most3. The tempting inference that the zero-indicator matrix inherits
that low rank is false. This matters because relation search needs zero locations,
not merely compact evaluation of all polynomial values.

The test generates nonsingular curves with a,b nonzero, full prime order q≠p,
and excludes embedding degrees1–4. It selects distinct factor-base x-coordinates
and a target using declared seeds. It builds both matrices, calculates ranks by
exact elimination modulo p, and verifies every zero entry by signed point addition.
The polynomial identity is checked for the first entry in each row, not every
entry; the generic bilinear identity itself also follows by expansion. No hidden
discrete-log table or root oracle is used.

| p | a | b | q | B | Seeds | Evaluation ranks | Zero-indicator ranks |
|---|---|---|---|---|---|---|---|
| 59 | 28 | 27 | 73 | 20 | 7,19,43 | 3,3,3 | 15,13,15 |
| 127 | 78 | 87 | 139 | 24 | 7,19,43 | 3,3,3 | 12,12,12 |
| 251 | 218 | 156 | 257 | 32 | 7,19,43 | 3,3,3 | 14,15,11 |

All158 zero entries passed signed group checks;228 sampled bilinear identities
passed. Every dataset refutes the asserted rank-at-most3 transfer. These tiny
ordinary prime-order curves are diagnostics only; they do not establish growing
zero-incidence rank, absence of other structure, or an n=5 complexity claim.
Finite sizes and seeds here serve falsification, not full-size extrapolation.

Astra's independent general counterexample is M_ij=x_i-x_j on distinct elements:
rank(M)≤2, but the zero-indicator is the identity, rank n. Entrywise zero testing
is nonlinear. Thus no general rank-transfer theorem justifies the shortcut.

## Costs, commands and reproducibility

Original command: `timeout 60 python3 /tmp/h001-sol-relations/falsifier.py`.
Original source hash: `6a914e8cd3876525471592fd12959974cc64674fc389b1a6f02b807dfa2aaeec`.
Original output is preserved as research/experiments/H001/relation_rank_original.json,
hash `b40ab1a929b932c91fe4f34f28ea51fb5a23bb1f09b664aff5802c09d8687286`.

Coordinator's archived source changes only output portability: import sys and
an optional output-path argument, defaulting beside the script. Source hash:
`e03be5152ae1958961eefe74526736ec7bc953b42ad2e007249ed8ef208bfa24`.
Reproduction:

```
timeout 60 python3 research/experiments/H001/relation_rank.py /tmp/H001_relation_rank_reproduced.json
```

Exit0. JSON compared equal after removing only elapsed_seconds and source_sha256.
All curve trials, coordinates, targets, seeds, edges, pivots, ranks and operation
counts match. Reproduced output archived, hash
`640e58b8a47a957e15dbe099ad262013f96df062b4e3941fca6eaaf9ab39c832`.
Each run used493728 explicitly instrumented events; both total987456. A run cap
of1M is enforced. Categories include modular operations, predicates, selected
matrix/point accesses, loops, random draws and all curve-generation trials.
This is not every Python instruction, bit cost, allocation cost or full solver
ledger. The3B² matrix-cell estimate excludes other data/runtime storage. Recorded
elapsed time is provenance only, not a throughput or GPU calibration claim.

`./scripts/check.sh > /tmp/ecdlp-h001-rank-check.log 2>&1` exited0, preserving the
accepted library. No new proof count contributes to an algorithmic result.

## Next action and limits

Reject low evaluation rank ALONE as a relation-predicate shortcut. Other algebraic
structure remains open but must identify a concrete extraction method with yield
and total-cost accounting. No additional rank experiment or machine refinement is
justified by these results. Continue broad independent H002 ideation, deduplicate
mechanisms, and test surviving hypotheses against the best applicable baseline.
Best supported reference remains square-root work; verified improvement NONE.
