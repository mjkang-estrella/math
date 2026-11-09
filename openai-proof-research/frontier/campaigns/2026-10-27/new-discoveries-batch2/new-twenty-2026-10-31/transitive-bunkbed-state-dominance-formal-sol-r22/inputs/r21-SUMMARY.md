# MathDB 382297 — partial implementation handback

Credit 0. Campaign 57/80 unchanged. No acceptance decision is made here.

## Proven and strictly checked

All fourteen immutable baseline modules were compiled from the empty build and independently kernel-checked. Their theorem audits passed.

Six new result modules passed compilation, independent kernel checking, and axiom audits. All audited dependencies are contained in {propext, Classical.choice, Quot.sound}.

- BunDomAbstract: sum invariance under reflection; paired-sum nonnegativity; one-step and all-time reflected mass dominance for nonnegative integer kernels, equivariance and forbidden strict crossing; antisymmetric nonnegative-above-diagonal payoff consequence. The finite summation universe is an arbitrary reflection-closed Finset of Nat pairs, fixed across the recursion.
- BunDomFiber: explicit assignmentEquiv and inverse laws using the actual Asg/res/fresH/fresV definitions; each restriction fiber is equivalent to (Fin (j+1) → Bool → Bool) × Bool and has cardinality 2^(2*j+3). This verifies 2*j+2 horizontal fresh bits plus one vertical bit. This is the total fiber count, not the four increment counts.
- BunDomPins: arbitrary finite Boolean pin equivalence, count of all-false restrictions, and count of at least one true relevant bit.
- BunDomZero: fresh-coordinate equivalence and cardinality when an arbitrary subset of horizontal coordinates is pinned false; the vertical bit remains free. Its exponent uses the cardinality of that coordinate subset, not yet R.card+S.card.
- BunDomRecursion: res_join, actual hor_join witness identity, actual stf_join update, generic count_transport and sum_transport. These retain dependence on the full prefix/fresh coordinates and are NOT the required count-only recursion.
- BunDomEndpoint: stf_at_source, unconditional source_bottom_mem, and source_inequality for j=u. The strict u<j case is NOT proved.

## Unpaid target

Step 4 was NOT reached in full. The exact intended statement, with the actual definitions and no added premise, is:

```lean
∀ (n u j : Nat), u ≤ j → j < n → Fintype.card {w : Bun.Asg n j // j ∈ Bun.sval true (Bun.stf n u j w)} ≤ Fintype.card {w : Bun.Asg n j // j ∈ Bun.sval false (Bun.stf n u j w)}
```

- Step 2: four actual increment-specific prefix fiber cardinalities; even count_increment_zero is not closed.
- Step 3: stateCount recursion compressed to old cardinalities, initial half/half cardinality law, and actual weight equivariance/no-crossing.
- Step 4: inequality for u < j < n; integer payoff identity and its application to the actual fibers.
- The attempted specialization count_recursion_full remains unproved (200000-heartbeat whnf limit); only general count_transport and sum_transport are green.

## Failed attempts and alternative route

Every invocation has a uniquely labeled receipt with its actual exit. results/382297.json lists all failures. No unchanged retries or increased limits were used. The specialized stateCount transport repeatedly exhausted the default 200000 heartbeats at whnf despite explicit predicate instantiation and a local opacity attempt; its last source is preserved in attempts/BunDomRecursion_v5.lean. The final green BunDomRecursion keeps the successfully verified general transport instead, without claiming the specialized or compressed recurrence.

The direct actual (0,0)-fiber count is retained in src/BunDomIncrementCounts.lean as a FAILING attempt (increment_zero_v2, exit 1). Its unresolved goals are the transformed finite sum cardinality and the transport integrand identity. It has no olean and is excluded from strict_green_modules. A genuinely different counting route through pinEquiv and zeroFreshEquiv produced the verified generic counting results above, but did not finish the actual four fibers. BunDomCountTools is a failed declaration-name probe, also excluded. No incomplete module is represented as green.

No Reach bridge was attempted. No protected peer was accessed; baseline source copies were replayed only within this lane. No baseline/helper/input edits, network, installs, git, children, alternate models, forbidden proof mechanisms or mathematical programs were used. Lean ran only through the provided wrappers. Frozen verification and the final manifest seal follow this report.
