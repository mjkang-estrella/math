# Lean bridge — status (2026-10-29)

**Toolchain verified working:** Lean 4.34.1 (`/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean`, commit 5045d0056413266e57c625dcd7c365b10e377c52) + Mathlib `.lake/packages/mathlib` (rev `d13f23b723b8a846827a245b89c10fc7d3f11612`) at
`/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal`.
Compile command: `lake env lean <file>` from that root.

**`lean/Bridge.lean` compiles** with two `sorry`-marked theorem statements (`G4_nonneg`, `G5_nonneg`). It is a **bridge, not a proof** — do not credit it as one.

## What a complete formalization requires

1. **Denumerant quasi-polynomials** (Prop 2.2, 2.3 of PROOF-K4-K5.md) as exact `ℚ`-valued identities on `ℕ` with divmod residue bookkeeping. Prop 2.2 has a full paper proof (two counting lemmas); Prop 2.3's exactness rests on the classical denumerant quasi-polynomial structure (paper sketch given).
2. **Newton certificate lemmas** (Lemma 3.1 univariate, 3.2 bivariate staircase): exact Newton-forward-difference expansions; Mathlib has `Polynomial`/`finset` tooling but the mixed-difference staircase lemma needs writing.
3. **The certificate tables** as finite `decide`-able checks: 15 classes (k=4 regime A3), 225 (k=4 A4), 2×2×11025 slabs + 2×11025 wedges + 11025 quadrant (k=5). Each class is 4–10 rational evaluations; a generated `.lean` file with `norm_num`/`decide` per class is mechanical but large (est. 10⁵–10⁶ lines; better: a `native_decide`-free generated tactic loop over an inlined data array).
4. **Regime decomposition bookkeeping** (Lemmas 1.1, 1.2 + the wedge/strip covering argument).

Estimated effort: 1–2 weeks of focused work. Not attempted in this session.

## Fallback verification status

The paper proofs rest on **complete exact-arithmetic class enumerations** (not samples, not floats):
- `checks/run4_k4_proof.py` — k=4: 15 + 225 classes, 0 failures (log `checks/logs/run4_k4_proof.log`)
- `checks/run6_k5_proof.py` — k=5 tail quadrant: 11025 classes, 0 failures
- `checks/run7_k5_regimes.py` — k=5 slabs + wedges: 0 failures; regime formulas cross-checked
- `checks/run8_k5_close.py` — k=5 R1/R2 slabs: 0 failures; T₅ vs direct series: 27 009/27 009 match
- `checks/logs/prop22_verify.log` — Prop 2.2 vs series, all r<15, Q≤20: 0 mismatches
