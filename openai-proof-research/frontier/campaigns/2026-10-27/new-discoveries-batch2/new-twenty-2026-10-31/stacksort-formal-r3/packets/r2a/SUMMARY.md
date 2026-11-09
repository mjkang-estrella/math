# Round 2A: partial implementation, not acceptance

The requested injections are NOT closed. No self-acceptance or credit is claimed. Root decides. No work on ExactSeeds20 was undertaken.

Completed, without new assumptions in the environment:

- `doubling_of_injection : DoublingInjection → Doubling`, including factorial conversion;
- root insertion, explicit inverse by maximum split, forward preservation of equal sorted outputs under increasing relabellings, and recovery of original words;
- `fixed_split_bound : ∀ a b, P a * P b ≤ P (a+b+1)`, with an actual finite injection using the two contiguous label blocks;
- `four_mul_P_le : ∀ n, 0 < n → 4 * P n ≤ P (n+1)`, by four disjoint families with both independent end choices, including the two cross families;
- a computable structural bottom-up recursion G, its seed and recurrence equations, monotonicity, and `G_le_P : RootSplit → ExactSeeds20 → ∀ n, G n ≤ P n`;
- all 110 numeric recurrence rows from 21 through 130, checked in the kernel against a literal table using the proved factorial formula for binomial coefficients;
- `G_130_eq_lower130 : G 130 = lower130`;
- `lower130_of_seeds : RootSplit → ExactSeeds20 → Lower130`.

NOT completed: DoublingInjection (the disjoint shuffle over all label subsets and its choose cardinality), RootSplit (the interior label-subset families and cardinal assembly), an unconditional doubling_proved, or endpoints conditional only on ExactSeeds20. The name lower130_of_seeds has an explicit RootSplit parameter; it is not the stronger requested statement.

The new source endpoints in StackSortInj2Final.lean are conditional on exactly DoublingInjection, RootSplit, and ExactSeeds20. This replaces the opaque Lower130 hypothesis by a proved numerical and inductive linkage. Both round-1 endpoint declarations and all 11 frozen source modules are unchanged. The maximum-fibre reading remains unconditionally proved upstream.

Validation evidence, module hashes, and audit totals are in results.json; replay commands are in REPRODUCE.md. All new module names start StackSortInj2. No git, external messages, upload, network, browser, child agent, publication, or shared ledger edit was used. All artifacts and temporary files are lane-local. No background job is retained at handback.
