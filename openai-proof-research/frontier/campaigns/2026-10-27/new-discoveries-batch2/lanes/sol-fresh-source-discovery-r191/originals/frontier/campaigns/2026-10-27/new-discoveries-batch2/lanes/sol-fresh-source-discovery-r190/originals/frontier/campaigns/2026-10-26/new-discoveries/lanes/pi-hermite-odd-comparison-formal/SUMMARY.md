# Lane Summary — `pi-hermite-odd-comparison-formal`

Supporting Lean component for the parent-hermite-bound proposal
(`../PROOF.md`, Sections 3 and 5): a **generic ODE sine comparison** and a
**strict energy-loss theorem**, proved for the raw first-order ODE system with
**no assumed positivity of `f`**.

**Status:** complete and machine-checked. This is a *supporting* lane earning
0 credit; the parent candidate remains **unaccepted** and all parent-owned
steps (M-monotonicity, Hermite initial-Gamma identities, Wallis bridges,
Cramér tail, final conjecture) are untouched here.

---

## 1. Scope

File: `formal/Comparison.lean` (703 lines, namespace `HermiteEnvelope`).

Generic setting (`E ≥ 7`, `A > 0`, `f g : ℝ → ℝ`):

* `∀ t, HasDerivAt f (g t) t`
* `∀ t, HasDerivAt g ((t ^ 2 - E) * f t) t`
* `f 0 = 0`, `g 0 = A`

No other hypotheses on `f` or `g` are used anywhere — in particular **no
positivity, sign, or size assumption on `f`** enters any proof. The only
allowed hypotheses are the ODE system itself, `E ≥ 7`, `A > 0`, the
initial conditions, and standard regularity (`Continuous f/g`) derived from
the ODE by `HasDerivAt.continuousAt`.

### Theorem A — `sine_comparison` (PROOF.md §3)

For all `0 ≤ x ≤ x0 := √(2/E)`:

```
A/√E · sin(√E x) ≤ f x ≤ A/√q0 · sin(√q0 x),   q0 = E − 2/E.
```

Proof architecture (no residual hypotheses):

* `duhamel_identity` — exact variation-of-constants (Duhamel) identity
  `√q · f x = A sin(√q x) + ∫₀ˣ (s² − E + q) f s sin(√q (x−s)) ds` for any
  `q ≥ 0`, proved by the Wronskian combination
  `W(s) = sin(√q (x−s)) g s + √q cos(√q (x−s)) f s` whose derivative is
  `(s² − E + q) f s sin(√q (x−s))` (`wronskian_deriv`), then the exact
  fundamental theorem of calculus (`integral_eq_sub_of_hasDerivAt`).
* **Lower bound**: the Duhamel integral at `q = E` is nonneg because
  `f ≥ 0` on `[0, x0]` and the kernel `sin(√E (x−s)) ≥ 0`
  (since `√E x ≤ √2 < π`).
* **Positivity of `f` (`odesys_pos`) is *proved*, not assumed** — this is the
  genuine content requested by the task:
  1. `odesys_pos_near_zero`: positivity on `(0, δ)` from `g 0 = A > 0`
     (`f` strictly increasing near 0).
  2. Beyond `δ`: a first zero `z ≤ x0` is taken as the *least* bad point of
     the compact set `S = [δ, x0] ∩ f⁻¹((−∞, 0])`
     (`IsCompact.of_isClosed_subset` + `IsCompact.exists_isMinOn`).
     Minimality gives `f > 0` on `(0, z)`; the Duhamel identity at `z`
     (`q = E`) then has a nonnegative integral term and the sine term
     `A sin(√E z) > 0` (kernel positive since `√E z ≤ √2 < π`), forcing
     `f z > 0` — contradiction.
* **Upper bound**: Duhamel at `q = q0`; the kernel `(s² − 2/E) f s ≤ 0`
  (from `s² ≤ x0² = 2/E`) times `sin(√q0 (x−s)) ≥ 0`.

### Theorem B — `energy_loss` (PROOF.md §5)

With `B(x) = genEnergy E f g x = (E − x²) f(x)² + g(x)²`:

```
B(x0) < A² (1 − 1/(2E²)),   x0 = √(2/E).
```

* `genEnergy_deriv_raw`: exact pointwise derivative `B'(x) = −2x f(x)²`
  (the `f g` / `g f` cross terms cancel **exactly** — no estimate).
* Exact FTC: `B(x0) = A² − ∫₀^{x0} 2s f(s)² ds` (no approximation).
* `loss_integral_lower`: `∫₀^{x0} 2s f(s)² ds ≥ 25A²/(36E²)`, from the lower
  sine comparison (Theorem A), the substitution `u = √E s`
  (`integral_comp_mul_left`), and the explicit bound
  `∫₀^{√2} u sin²u du ≥ 25/72` via splitting `[0,1] ∪ [1,√2]` with
  `sin u ≥ sin 1 ≥ 5/6` on `[1, √2]` (`sin_ge_x_sub_cube_div_six`,
  `sin_one_ge_five_six` — Taylor `x − x³/6 ≤ sin x` from `∫cos = sin` and
  `cos ≥ 1 − t²/2`).
* Ratio `25/36 > 1/2` finishes.

### Auxiliary exact facts (all proved, none assumed)

`odesys_continuous_f/g`, `odesys_nonneg`, `sqrt2_lt_pi`,
`sqrt2_le_pi_div_two`, `q0_pos`, `sqrtE_mul_short_le_sqrt2`,
`sqrtq0_mul_short_le_sqrt2`, `sin_le_self_of_nonneg`, `two_cos_ge`
(`cos t ≥ 1 − t²/2`), `sin_ge_x_sub_cube_div_six`, `sin_one_ge_five_six`,
`lower_integral_nonneg`, `upper_integral_nonpos`.

---

## 2. What is NOT done (parent-owned / out of scope)

* M-monotonicity of the Hermite envelope, initial-Gamma identities, the
  Wallis-bound bridge to the Gamma function, the Cramér tail comparison, and
  the final conjecture — all belong to the parent lane.
* This lane does **not** prove the *strict* lower inequality
  `A/√E sin(√E x) < f x` for `x > 0` (only `≤` is needed downstream).
* `Comparison.lean` is self-contained: it imports only the frozen
  `SourceDefs` (for namespace conventions); it uses none of the frozen
  `Energy`/`WallisBounds` declarations. The three frozen modules were still
  byte-identically copied and compiled so the lane mirrors the parent
  environment (their oleans are also prerequisites of the toolchain path).

---

## 3. Toolchain and replay commands

* Lean: `/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean` (v4.34.1)
* Mathlib: pinned `d13f23b7` at
  `/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib`
* Runner: `run_lean.py` (sets `LEAN_PATH`), `warningAsError true` set in-file.

Replay (from `formal/`):

```bash
python3 run_lean.py -o SourceDefs.olean SourceDefs.lean       # exit 0, silent
python3 run_lean.py -o Energy.olean Energy.lean               # exit 0, silent
python3 run_lean.py -o WallisBounds.olean WallisBounds.lean   # exit 0, silent
python3 run_lean.py -o Comparison.olean Comparison.lean       # exit 0, silent
python3 run_lean.py logs/axiom_check.lean                     # prints #print axioms
```

Logs: `logs/build_*.log` (all empty = zero errors/warnings under
`warningAsError true`), `logs/axiom_check.log`.

### Frozen-module integrity (re-verified after final build)

```
3ef55bfccb36835fc4c09e20a4545d2a7eb7283ba2b7bea08df8e8f594943ed0  SourceDefs.lean
7c78e64fa4d165c22f7928a8efb343b58a180d4f877938cc24635543d68e7a55  Energy.lean
5d1e2aa48f8163158061cd6354b333d8d1592b3635abd79e6e4df9b44940dee3  WallisBounds.lean
```

Byte-identical to the frozen copies at commit `2b7910d4e1`
(produced olean sizes also match the parent's: 363312 / 556000 / 786168 bytes).

---

## 4. Axiom audit

`logs/axiom_check.lean` runs `#print axioms` on all 11 public declarations
(`odesys_continuous_f/g`, `duhamel_identity`, `odesys_pos_near_zero`,
`odesys_pos`, `odesys_nonneg`, `sine_lower`, `sine_upper`,
`sine_comparison`, `genEnergy`, `energy_loss`). Every one reports exactly

```
[propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, `native_decide`, `unsafe`, or `axiom` declarations
appear anywhere in `Comparison.lean` (grep-verified).

---

## 5. Honest gaps / caveats

* The generic ODE system here is the *raw* first-order system. The parent
  proposal's `f, g` are the specific Hermite-envelope objects; the parent
  must supply the ODE hypotheses (`E ≥ 7`, the two `HasDerivAt` facts,
  `f 0 = 0`, `g 0 = A`) for its concrete functions to instantiate
  `sine_comparison` / `energy_loss`. That instantiation is parent-owned.
* `energy_loss` gives the strict loss at the single endpoint `x0 = √(2/E)`;
  the parent's §5 also tracks energy on sub-intervals — again parent-owned.
* The comparison constants are exactly as in PROOF.md: `A/√E sin(√E x)` and
  `A/√q0 sin(√q0 x)` with `q0 = E − 2/E`; the loss bound is proved with the
  weaker constant `25A²/(36E²)` (from `sin 1 ≥ 5/6`), which is strictly
  stronger than the required `A²/(2E²)` since `25/36 > 1/2`.
* `genEnergy` is a fresh definition in this namespace (`HermiteEnvelope.genEnergy`);
  if the parent's `Energy` module defines its own energy functional, the
  parent needs a one-line definitional bridge (both are `(E − x²) f² + g²`).
