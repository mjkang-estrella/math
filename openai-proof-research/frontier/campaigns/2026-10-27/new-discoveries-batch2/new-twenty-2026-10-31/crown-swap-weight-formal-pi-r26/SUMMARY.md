# SUMMARY — crown-swap-weight-formal-pi-r26

**Result:** sealed. `CrownVSwapWeight` compiles strict (`-DwarningAsError=true`, exit 0,
first attempt), passes the actual module-name `checker.sh CrownVSwapWeight` under the
pinned lean 4.34.1 PATH, and the ONE new declaration closes within
{propext, Classical.choice, Quot.sound}.

**Deliverables (all hashes in `manifest.json`, re-verified in `postcheck.json`):**

| Artifact | Hash (sha256, head) | Receipt exit |
|---|---|---|
| `src/CrownVSwapWeight.lean` | `920ff80e…c61e4c1` | — |
| `build/CrownVSwapWeight.olean` | `c5bc8634…972b1d` | — |
| strict build receipt | `cb2058…` (see manifest) | 0 |
| module checker receipt | `e7305a…` (see manifest) | 0 |
| single-decl axiom audit receipt | `3a7854…` (see manifest) | 0 |

**Scope paid:** the ACTUAL strict natural finite-prefix WEIGHT DESCENT
`CrownV.swapAlloc_weight_strict`: for ALL `m i j : Nat`, `a : Nat → Nat` with `i < j < m`
and `0 < a j`, `∑ k < m, k * swapAlloc a i j k < ∑ k < m, k * a k` — about the real
double `Function.update` swap allocation, no proxy, no capacity or desired-weight
premise, no conclusion-encoding hypothesis. Exact truncated-subtraction, `a j = 1` and
saturation boundaries handled by the exact hypotheses.

**Scope unpaid:** normalization existence, finite-block bridge, ideal certificates and
all later pipeline stages plus the full audit / negative controls / extracted replay /
independent review / acceptance — recorded verbatim in `results/369163.json`. r22
uniqueness / r21 prefix / r24 capacity / r25 total remain scoped preserved milestones.
Campaign 52/60 unchanged; credit 0.

**Integrity:** 1350/1350 frozen inputs intact before and after (`frozen-before.json`,
`frozen-after.json`); r23/r24/r25 artifacts untouched; all runner groups reaped; unique
receipts with true exits; sampled RSS peaks labelled as sampled.
