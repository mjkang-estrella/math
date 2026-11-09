# SUMMARY — crown-greedy-normalization-formal-pi-r27

**Result:** sealed. `CrownVGreedyNormalize` compiles strict
(`-DwarningAsError=true`, exit 0 after three retained diagnostic repairs), passes
the actual module-name `checker.sh CrownVGreedyNormalize` under the pinned lean
4.34.1 PATH, and ALL FOUR new declarations close within
{propext, Classical.choice, Quot.sound} (the two defs depend on no axioms).

**Endpoint (paid, this milestone):** for EVERY `m r : Nat` and
`d a : Nat → Nat` with `∀ k < m, a k ≤ d k` and `∑_{k<m} a k = r`, there exists `b`
reachable from `a` by a finite `Relation.ReflTransGen` chain of genuine legal swaps
(`LegalSwap` = actual `swapAlloc a i j` update with `i < j < m`, `a i < d i`,
`0 < a j` — no conclusion encoded in the relation) such that `b` keeps prefix
capacity, keeps total `r`, is terminal (underfull earlier ⇒ later zero), and
`b k = greedyStep d r k` for every `k < m` via paid r22 uniqueness. No `m > 0` or
positive-budget premise; empty/zero cases in the same universal statement;
outside-prefix values untouched.

**Mechanism:** paid r26 strict natural weight descent
`swapAlloc_weight_strict` + structural induction on a weight bound; paid r24/r25
capacity/total preservation carried through each swap; terminal uniqueness from
paid r22. The r22/r21/r24/r25/r26 baselines were NOT recompiled — scoped readonly
imports only.

**Deliverables (all hashes in `manifest.json`, re-verified in `postcheck.json`):**

| Artifact | Hash (sha256, head) | Receipt exit |
|---|---|---|
| `src/CrownVGreedyNormalize.lean` | `f884e828…ca81c55` | — |
| `build/CrownVGreedyNormalize.olean` | `3c6f0dac…2fe093a` | — |
| strict build receipt | `c5ac18d5…acc3a3` | 0 |
| module checker receipt | `89dc48fe…f77252` | 0 |
| four-decl axiom audit receipt | `00ab44fb…db072c0` | 0 |

Three earlier exit-1 attempt receipts retained as true diagnostic history; no
unchanged recompilation, no stale-olean pass.

**Scope paid:** the ONE coherent normalization endpoint above — existence of a
finitely reachable terminal allocation canonically equal to the actual
`greedyStep d r` on the prefix.

**Scope unpaid:** finite-block bridge, monomial/ring-ideal certificates, full
audit/negative controls/extracted replay/independent reviews/paper/acceptance —
recorded verbatim in `results/369163.json`. Credit 0; campaign 52/60 unchanged.

**Integrity:** 1404/1404 frozen inputs intact before and after
(`frozen-before.json`, `frozen-after.json`); prior crown lanes untouched; all
runner groups reaped; unique receipts with true exits; sampled RSS peaks labelled
as sampled.
