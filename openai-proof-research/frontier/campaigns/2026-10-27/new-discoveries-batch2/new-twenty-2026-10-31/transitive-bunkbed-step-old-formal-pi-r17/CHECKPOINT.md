# R17 checkpoint — transitive-bunkbed-step-old (MathDB 382297 auxiliary, credit 0, campaign 52/60)

## Status: MILESTONE SEALED (strict)

Single milestone reached and sealed: the actual `Bun.stepU` update preserves membership
of every old index. For arbitrary `m k : Nat`, `R S : Finset Nat`, `x y z sigma : Bool`
with `k != m`:

    Bun.stepU_old_mem_iff :
      k ∈ Bun.sval sigma (Bun.stepU m R S x y z) <-> k ∈ Bun.sval sigma (R, S)

Both indicator truth values and both layers are covered; no finiteness, enumeration,
proxy update, or conclusion-encoding premise. The auxiliary component lemma
`Bun.mem_stepU_component` covers either truth value of the insert indicator.
`BunState` imported unchanged; `stepU`/`sval`/`ind` untouched.

## Scoped #print axioms (from build log, runner-capped)

    'Bun.mem_stepU_component' depends on axioms: [propext, Classical.choice, Quot.sound]
    'Bun.stepU_old_mem_iff' depends on axioms: [propext, Classical.choice, Quot.sound]

No sorry/admit/new axiom/unsafe/partial/native_decide. First compile attempt had one
error (reverse direction of the component lemma); repaired from the actual diagnostics;
final build exit 0, postcheck (`checker.sh BunStepOld`, module name) exit 0.

## Hashes (full manifest: audit/manifest-r17.json)

- src/BunStepOld.lean      5649af1f7374c907... (sha256 in manifest)
- build/BunStepOld.olean   19a94323afba2907...
- build receipt JSON       3b839c7dfb548df9... (receipt/1794017048043988787_lean_BunStepOld.json)
- postcheck receipt JSON   48348964a1b7dc5e... (receipt/1794017070157461100_leanchecker_BunStepOld.json)
- frozen-before/after      825/825 verified, zero mismatches, both recorded

## Exact unpaid list (nothing below is claimed done)

1. Full recursive `stf` old-index stability (the r16 original target; this module is a
   pure helper, not a replacement).
2. New-index indicators beyond the closed form (new indicators).
3. Prefix-recursion Reach joint induction.
4. Token fibers.
5. Correct reflection.
6. Terminal payoff.
7. Count / cardinality endpoint.
8. Deep audit; negative controls.
9. Extracted strict replay from clean checkout.
10. Independent statement-fidelity and proof reviews.
11. Paper; acceptance. Credit remains 0; campaign 52/60 unchanged.

R16 produced no target source/receipt; this round's artifacts are the first. Frozen
inputs preserved before and after; no baseline replay performed; development imports
read-only. Lane handback on disk complete.
