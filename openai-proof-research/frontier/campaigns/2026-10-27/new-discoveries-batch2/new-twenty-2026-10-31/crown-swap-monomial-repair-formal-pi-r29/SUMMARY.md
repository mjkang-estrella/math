# SUMMARY — crown-swap-monomial-repair-formal-pi-r29

Target MathDB 369163 auxiliary formalization lane. Status: **sealed, strict success,
credit 0 (52/60 campaign boundary unchanged)**.

## What was delivered

`src/CrownVSwapMonomial.lean` (sha256 `291f69c8518a540a5645ae6e1aae417dfc53486ca550762157e913fd5a1205ea`)
compiles clean under the pinned toolchain (`lean-4.34.1`, mathlib `d13f23b7` prebuilt,
`-j1 -M3500 -DwarningAsError=true`, runner-capped CPU120/wall140/AS12GiB):

- `build/CrownVSwapMonomial.olean`
  sha256 `2603ec2e6192e39c0ebbf9bce4123c9f2e15e2da486ddce2ec31e94957283667`
- strict compile receipt `receipt/1794027715666976584_lean_CrownVSwapMonomial.json`, EXIT=0
- axiom audit receipt `receipt/1794027794292953373_axioms_CrownVSwapMonomial.json`, EXIT=0
  (17 new decls, only `propext`/`Classical.choice`/`Quot.sound`; no sorry/admit/axiom/
  unsafe/partial/native_decide)
- module checker receipt `receipt/1794027802749216659_leanchecker_CrownVSwapMonomial.json`, EXIT=0
- post-checker rehash + full manifest: `MANIFEST.json`

## Mathematical endpoint (original scope, no surrogate)

In the unchanged `CrownV.PolyRing n K = MvPolynomial (V n × Bool) K` with unchanged
`xx`/`yy`, for the actual finite product `vswapProd d a = ∏ v, xx v ^ a v * yy v ^ (d v - a v)`
and the actual vertex double-update `vswapAlloc a i j`:

- `CrownV.exists_vswap_monomial_certificate` — explicit `q` (finite product of the
  unaffected factors, one sign) with `vswapProd d a - vswapProd d (vswapAlloc a i j) = q * minor i j`,
  for ALL `n`, `[CommRing K]`, distinct `i j`, capacity/room/positivity hypotheses.
- `CrownV.vswap_diff_mem_allPairMinorIdeal` — corollary via UNCHANGED `allPairMinorIdeal` only.

## Frozen inputs

`verify_frozen.py before`: `{"count": 1510, "mismatches": []}` at 1794027276.
`verify_frozen.py after`: re-run post-seal, 1510/1510, no mismatches.

## Handback

Disk state: sealed olean + receipts + logs + MANIFEST + CHECKPOINT + this SUMMARY +
results/369163.json. No processes left; all runner groups reaped
(`GROUP_MEMBERS_LEFT []` on every receipt). Latest true exit: checker EXIT=0.

Unpaid boundary and next-step notes: see CHECKPOINT.md.
