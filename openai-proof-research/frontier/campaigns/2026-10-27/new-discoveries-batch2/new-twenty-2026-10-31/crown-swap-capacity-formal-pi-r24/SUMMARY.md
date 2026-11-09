# SUMMARY — crown-swap-capacity-formal-pi-r24

**Result:** sealed. `CrownVSwapCapacity` compiles strict (`-DwarningAsError=true`, exit 0,
first attempt), passes the actual module-name `checker.sh CrownVSwapCapacity` under the
pinned lean 4.34.1 PATH, and all SIX declarations close within
{propext, Classical.choice, Quot.sound} — in fact only propext and Quot.sound appear.

**Deliverables (all hashes in `manifest.json`, re-verified in `postcheck.json`):**

| Artifact | Hash (sha256, head) | Receipt exit |
|---|---|---|
| `src/CrownVSwapCapacity.lean` | `fd2e8a5f…` | — |
| `build/CrownVSwapCapacity.olean` | `7c80ab9d…` | — |
| strict build receipt | `eef38fc1…` | 0 |
| module checker receipt | `d50324a1…` | 0 |
| six-decl axiom audit receipt | `79856e57…` | 0 |

**Scope paid:** the actual double-update swap allocation and its pointwise helpers, plus
prefix capacity preservation (`swapAlloc_capacity`) — exact copied statements, no proxies.
Six declarations: `swapAlloc` (def), `swapAlloc_eval`, `swapAlloc_at_i`,
`swapAlloc_at_j`, `swapAlloc_at_else`, `swapAlloc_capacity` (theorems).

**Scope unpaid:** total-sum, weight descent, and all later pipeline stages — recorded
verbatim in `results/369163.json`. Credit 0; campaign 52/60 unchanged.

**Integrity:** 1245/1245 frozen inputs intact before and after
(`frozen-before.json`, `frozen-after.json`); r23 artifacts untouched; all runner groups
reaped; unique receipts with true exits; sampled RSS peaks labelled as sampled.
