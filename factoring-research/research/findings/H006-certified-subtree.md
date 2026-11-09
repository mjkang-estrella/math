# H006 finding: valid relaxed witnesses; finite screen inconclusive

Verified factoring complexity improvement: **NONE**. Independent mathematical
review is pending; the following records the parent's diagnostic and scope.

The [preregistered degree-five probe](../hypotheses/H006.md) strengthens H005,
whose degree-two intervals contained only one or two integer points. It builds
explicit witnesses for the relaxed inverse polynomial and expands only nodes
whose feasibility it certifies. Failure to construct a witness means unknown,
never infeasible. Hidden factors are confined to tiny input generation.

All 20 registered instances completed, four per K, in about 0.56 seconds total.
The exact input values and every trial's counters are in
[result.json](../experiments/H006/result.json).

| K | Median visited nodes | Median fraction of unpruned tree | Spurious certificates, four inputs |
|---:|---:|---:|---:|
| 12 | 12 | 0.4000 | 13 |
| 18 | 90 | 0.3571 | 168 |
| 24 | 614 | 0.3010 | 1,098 |
| 30 | 4,037 | 0.2466 | 7,937 |
| 36 | 22,337 | 0.1705 | 43,863 |

The registered rejection criterion was a median fraction at least 0.5 at the
largest completed size. It was **not met**. Preserve the disposition
**inconclusive**, regardless of later hypotheses about scaling. Many certified
points fail the original multiplication equation, showing that the relaxation
admits irrelevant branches on these inputs. Those counts neither establish an
asymptotic lower bound nor measure an early-stop factoring algorithm.

The witness constructor checks the modular equation and every tangent/secant
inequality exactly. High polynomial powers and partial sums use Python integers;
their widths are recorded, not treated as constant-cost arithmetic. The probe
does not implement or time a fixed-dimensional integer-programming solver.

Source and protocol hashes rechecked after execution:

- Source: `2ef3772294e3362e2952864e8ec8af322e34f2fc43d2a321cad4f1530b1ece28`.
- Protocol: `820ac9d1824c221fe5b4fb87f97302cc2c9935a32f9a484c06c279c2b8711727`.

Next: independent review of certificates, nested relaxation feasibility and
whole-tree work, including whether a counting argument gives a rigorous
obstruction. The full-tree/early-stop distinction must remain explicit. No
new solver or Lean complexity claim follows from this screen.
