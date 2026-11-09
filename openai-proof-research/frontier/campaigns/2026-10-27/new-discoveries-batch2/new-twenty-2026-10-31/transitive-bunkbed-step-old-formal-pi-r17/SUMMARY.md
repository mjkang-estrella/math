# R17 summary — BunStepOld (stepU old-index membership, exact iff)

Result (module `BunStepOld`, namespace `Bun`, imports `BunState` only):

- `Bun.mem_stepU_component (k m : Nat) (T : Finset Nat) (c : Bool) (hkm : k ≠ m) :
    k ∈ (if c then insert m T else T) ↔ k ∈ T`
- `Bun.stepU_old_mem_iff (m k : Nat) (R S : Finset Nat) (x y z σ : Bool) (hkm : k ≠ m) :
    k ∈ sval σ (stepU m R S x y z) ↔ k ∈ sval σ (R, S)`

Method: normalize `sval σ (stepU ...)` and `sval σ (R, S)` by `rfl` to the indicator
conditionals `(stepU ...).1/.2` and `R`/`S`; reduce each component by
`mem_stepU_component` (cases on the indicator; `Finset.mem_insert` plus `k ≠ m`);
case on `σ` for the selector. All hypotheses arbitrary; no proxy or conclusion-bearing
assumptions; both layers and both indicator truth values handled.

Machine facts: build exit 0 (wall 2675 ms, 2-CPU pinned, caps in receipt), olean
19a94323afba2907..., postcheck `checker.sh BunStepOld` exit 0. Scoped #print axioms on
both declarations: exactly propext, Classical.choice, Quot.sound. 825/825 frozen inputs
verified before and after; manifest audit/manifest-r17.json includes receipt-JSON hashes;
CHECKPOINT.md carries the exact unpaid list. Credit 0; campaign 52/60 unchanged.
