# MathDB 382297: state endpoint implementation handback

Credit 0. Campaign 57/80 unchanged. Root alone decides acceptance.

## Exact result

`Bun.state_endpoint` in `src/BunDomFinal.lean` proves, without any extra premise:

```lean
∀ (n u j : Nat), u ≤ j → j < n → Fintype.card {w : Bun.Asg n j // j ∈ Bun.sval true (Bun.stf n u j w)} ≤ Fintype.card {w : Bun.Asg n j // j ∈ Bun.sval false (Bun.stf n u j w)}
```

All eight new result modules passed `check32.sh` compilation and independent `checker32.sh` kernel checking. `BunDomAuditR22` audits all 30 new theorems; every dependency list is contained in {propext, Classical.choice, Quot.sound}. Twenty immutable baseline modules were imported, never recompiled or modified. Source/olean hashes and exact receipt labels are in `results/382297.json`.

## Proof and module dependencies

1. `BunDomRows`: arbitrary Boolean row-hit counts and an explicit independent-row fiber equivalence. Fixed horizontal outcomes x,y and vertical bit z have product cardinality.
2. `BunDomFiberSums`: fiberwise summation over x,y,z, the generic increment cardinality, and all four increment formulas. Writing A0,A1,B0,B1 for the two false/true row counts, the four weights are 2*A0*B0, A1*B0, A0*B1, and 2*A1*B1+A1*B0+A0*B1.
3. `BunDomActualCounts`: transports the product count to the actual res/hor/fresV fiber through a generic predicate equivalence. For sets supported in [0,j], the row counts are 2^(j+1-card) and 2^(j+1)-2^(j+1-card).
4. `BunDomCountLaw`: actual stepU cardinality update, fresh state count, and the full-prefix recurrence depending only on old cardinalities. `transport_dec` retains a supplied decidability instance; this removes the expensive instance conversion in the previous transport route.
5. `BunDomCompressed`: bounded finite state box, its reflection closure and actual state support, generic grouping by state, and the count-only recurrence.
6. `BunDomDominance`: actual kernel equivariance and no strict crossing; zero source mass below the diagonal; reflected count dominance for every u ≤ j < n. Source initialization uses the pointwise source support (first count 1, second count at most 1), which suffices; a separate half/half cardinality formula is unnecessary and is not claimed.
7. `BunDomPayoff`: the integer fresh endpoint count difference is A1*B0-A0*B1 = 2^(j+1)*(2^(j+1-b)-2^(j+1-a)). It is antisymmetric and nonnegative for a>b.
8. `BunDomFinal`: actual endpoint counts are sums over prefix fibers. Grouping their difference by state and applying the sealed abstract payoff theorem proves the strict successor case. The sealed source inequality handles j=u, giving the exact final endpoint.

The state function is locally irreducible during transport. A separate failure arose from also making stateCount irreducible during a `change`; keeping stateCount at its original reducibility resolved that conversion. Failed compile diagnostics and true exit codes remain in uniquely labeled receipts and outputs. Selected blocked sources are preserved under `attempts/`. There were no unchanged retries.

## Unpaid and scope

No obligation remains for the requested state endpoint. The Reach bridge was neither attempted nor accessed. Full Reach-level integration, independent acceptance and any novelty assessment remain outside this lane. This is a formal implementation of the supplied proof mechanism, not a claim of independent invention or new credit.

No children, alternate models, network, git, installs, solvers, forbidden proof mechanisms, or protected-peer access were used. All authored lane files used write_lane.py; local Python work used run.py; Lean used only the two supplied wrappers. Final frozen verification and the noncircular manifest seal follow this report.
