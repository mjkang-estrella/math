# CHECKPOINT — crown-swap-monomial-repair-formal-pi-r29 — SEALED 2026-11-06

State: **strict success sealed.** Module `CrownVSwapMonomial` compiled, axiom-audited,
module-checked, hashed. Latest true exits: compile EXIT=0, audit EXIT=0, checker EXIT=0.

## Chain of true-exit receipts (this run)

1. `1794027279513033888` lean compile, EXIT=1 — first diagnostics on root-repaired copy
   (stuck `CommMonoid ?m` / `CommRing ?m` instance metavariables).
2. `1794027435417531119` lean compile, EXIT=1 — after repair set A; invalid `.1/.2`
   projections (membership whnf-normalizes to two-constructor `List.Mem`).
3. `1794027715666976584` lean compile, **EXIT=0** — sealed build.
   olean sha256 `2603ec2e6192e39c0ebbf9bce4123c9f2e15e2da486ddce2ec31e94957283667`.
4. `1794027794292953373` axiom audit (`-j1 -M3500 -DwarningAsError=true`, same flags),
   **EXIT=0** — 17/17 new decls: only `propext, Classical.choice, Quot.sound`
   (`vswapAlloc`: none).
5. `1794027802749216659` `checker.sh CrownVSwapMonomial` (leanchecker, own runner
   receipt), **EXIT=0**. Source/olean/log rehashed AFTER checker; hashes in
   `MANIFEST.json`.

## Repairs made after first compile (persisted in src before seal)

1. `refine Finset.prod_congr ?_` → `refine Finset.prod_congr rfl ?_`
   (line 157: hole in the set-equality arg left the `CommMonoid` instance stuck).
2. `obtain ⟨q, hq⟩ := exists_vswap_monomial_certificate …` → pinned `(K := K)`
   (line 187: coefficient type otherwise an unresolved metavariable → stuck `CommRing ?m`).
3. `hx.1` / `(Finset.mem_erase.1 hx.2).1` →
   `(Finset.mem_erase.1 hx).1` / `(Finset.mem_erase.1 (Finset.mem_erase.1 hx).2).1`
   (lines 159–160: bare projection notation hits two-constructor `List.Mem`).

No proof logic, statement, definition, ring, or finite product was altered; the
explicit witness `q` and both theorems are exactly as drafted.

## Sealed endpoint

- `CrownV.exists_vswap_monomial_certificate`: for all `n`, `[CommRing K]`, all
  `d a : V n → ℕ`, distinct `i j` with `a ≤ d`, `a i < d i`, `0 < a j`, there is an
  explicit `q : PolyRing n K` (finite product of unaffected factors, one sign) with
  `vswapProd d a - vswapProd d (vswapAlloc a i j) = q * minor i j` in the UNCHANGED
  `MvPolynomial (V n × Bool) K`. Original arbitrary ring; zero ring / nilpotents /
  char 2 covered; `n = 0` vacuous via the same quantifiers.
- `CrownV.vswap_diff_mem_allPairMinorIdeal`: the same difference lies in the
  UNCHANGED `allPairMinorIdeal` (corollary only; no `graph-edgeJ` claim).

## Paid / unpaid boundary

Paid here: the one-swap monomial certificate + `allPairMinorIdeal` corollary, strict
compile, scoped axiom audit, module checker, hashes, manifest.

Unpaid (unchanged): Nat→vertex finite-block bridge to r27, multi-swap telescoping,
arbitrary coefficients / polynomial grouping, reverse rank-one kernel,
disjoint-components / Pc semantic bridge, original `J` / colons, homogeneous degrees
0..3 incl. char 2, quartic witnesses / VIs 4, full safety/type/audit
negative-controls, fresh extracted replay, independent review, paper, acceptance.
Credit 0; campaign 52/60 beyond 39 unchanged.

## Frozen inputs

1510 inputs verified before (`frozen-before` run) — re-verified after seal; see
`verify_frozen.py after` output recorded in SUMMARY.md. All r28 bytes untouched.
