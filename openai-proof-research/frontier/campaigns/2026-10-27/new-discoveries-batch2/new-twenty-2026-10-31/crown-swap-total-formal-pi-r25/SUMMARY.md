# SUMMARY — crown-swap-total-formal-pi-r25

**Result:** sealed. `CrownVSwapTotal` compiles strict (`-DwarningAsError=true`, exit 0,
first attempt), passes the actual module-name `checker.sh CrownVSwapTotal` under the
pinned lean 4.34.1 PATH, and BOTH new declarations close within
{propext, Classical.choice, Quot.sound}.

**Deliverables (all hashes in `manifest.json`, re-verified in `postcheck.json`):**

| Artifact | Hash (sha256, head) | Receipt exit |
|---|---|---|
| `src/CrownVSwapTotal.lean` | `5845aa54…` | — |
| `build/CrownVSwapTotal.olean` | `1537f62e…` | — |
| strict build receipt | `58da…` (see manifest) | 0 |
| module checker receipt | see manifest | 0 |
| two-decl axiom audit receipt | see manifest | 0 |

**Scope paid:** the swap finite-prefix TOTAL-SUM PRESERVATION `swapAlloc_total` (all
`m i j`, `a` with `i < j < m`, `0 < a j`: prefix sums of the actual swap allocation
equal prefix sums of `a`) plus its supporting pointwise unit-balance identity
`swapAlloc_shift`. Exact copied statements about the real `Function.update` swap; no
proxies, no capacity premise, no conclusion-encoding hypotheses. Two declarations,
both theorems; `CrownVSwapCapacity` imported sealed, not redefined.

**Scope unpaid:** weight descent, normalization, finite-block bridge, ideal
certificates and all later pipeline stages — recorded verbatim in
`results/369163.json`. Helper earns 0 credit; campaign 52/60 unchanged.

**Integrity:** 1297/1297 frozen inputs intact before and after (`frozen-before.json`,
`frozen-after.json`); r23/r24 artifacts untouched; all runner groups reaped; unique
receipts with true exits; sampled RSS peaks labelled as sampled.
