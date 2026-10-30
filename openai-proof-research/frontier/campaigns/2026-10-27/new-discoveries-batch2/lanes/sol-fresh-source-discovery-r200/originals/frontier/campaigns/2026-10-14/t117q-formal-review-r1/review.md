# T117Q scoped formal-support review r1

Verdict: **PASS_SCOPED_T117Q**. No required repairs.

Scope of this verdict: the frozen Lean support packet `t117q-formal-v1` only. This review issues no
mathematical full-proof, contribution, manuscript, acceptance or count verdict. The earlier
PASS_FULL_T117Q proof gate and round-1 SUBSTANTIAL contribution gate created no formal presumption
here, and round-2 contribution positioning remains pending outside this review.

## 1. Authentication (performed before reading the inventory)

- External anchor: `manifest.json` SHA256 `b741e2d76e9383238b5f3e975c634e2bb48b75eaa00dc1fb93371b0a1c139b37` (matches).
- `T117Q.lean` `bdb2a4d205043cc71517e49123a32855a712f066fe860b53c0cee9f40d8cfa9f`, `Controls.lean`
  `c5a574b41a5f9341216ed95635eacd5bcd585baf99b1c01756b1a212baedf2fb` (match dispatch and manifest).
- Packet `verify.py`: correct anchor PASS (exit 0). Three wrong anchors (all zeros, the
  development inventory hash `0be6379a…81a6`, the true anchor with its last digit changed) all fail
  with `external anchor mismatch` (exit 1). Logs: `logs/verify-*`.
- Copied integrity controls (`integrity_controls.py`, `/var/tmp` copies only): all 15 cases have the
  expected outcome and reason (positive accepted; wrong/malformed anchor, changed/missing source,
  extra file/directory, root/ancestor/payload symlink, payload/manifest hardlink, FIFO, nested
  manifest and self-reseal rejected). Log: `logs/integrity-controls.out`.
- Development provenance: `t117q-formal-development-r1/inventory.json` hashes to
  `0be6379a…81a6`, identical to the retained copy inside the packet. Relative to that inventory, the
  only changed file is `README.md` (packet path and the enlarged-packet paragraph). Sources,
  lockfile, builder and `validation/` are byte-identical. The packet adds `inputs/`,
  `integrity_controls.py`, `verify.py`, `packaging-provenance.json` and `manifest.json`.
- Input identities: `inputs/candidate.md` `e32f7a12…aeea4`, `inputs/author-MANIFEST.json`
  `053986e5…28ae2`, `inputs/original-scope.txt` and `inputs/contribution-response.md` match their
  origin files byte for byte.
- Immutability: a full listing of the packet (type, link count, mode, size, path) and SHA256 values of every file was
  captured before and after all runs (`logs/packet-state-{before,after}.txt`) and is identical. The
  anchor still verifies afterwards. Tracked files in all 9 dependency checkouts remain clean.

## 2. Reading

The review read the full `T117Q.lean` (219 lines), `Controls.lean` (82), `README.md`, `provenance.json`,
`packaging-provenance.json`, `inventory.json`, `manifest.json`, `rebuild.py`, `verify.py`,
`integrity_controls.py`, `probe.py`, `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`,
`validation/*`, and `inputs/candidate.md` in full, with emphasis on §3 and §8. It also read
`Matrix.le_iff` and `IsHermitian.eigenvalues_eq_zero_iff` in the pinned mathlib. Development-failure logs were read only
as provenance. Both were `Controls.lean` proof-script errors in `positive_threshold_necessary`
(an earlier source hash `3cc85afe…`), and the support file compiled cleanly in both. They have no
bearing on the successful validation, which was reproduced separately (section 3).

Source scan: no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`,
`set_option`, attributes, instances, notation, macros or `lemma`/`abbrev`/`opaque` declarations.
Only `def`/`noncomputable def`/`theorem` occur, so the builder's declaration regex sees every user
declaration.

## 3. Independent fresh build and kernel audit

- Toolchain: Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`, binary SHA256
  `e8baaa71…5550`. All 9 lockfile pins match the cache checkouts (`git rev-parse HEAD`),
  including mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. The tracked trees are clean.
- `rebuild.py --output /var/tmp/t117q-formal-review-r1-rebuild-<epoch>` (new, unused; exact path in
  `logs/rebuild-output-path.txt`): `PASS_SCOPED_SOURCE_BUILD_TYPES_AND_STANDARD_AXIOMS`, 31 support +
  15 control declarations, empty compile logs (no errors or warnings). Every one of the 46 depends exactly on
  `propext, Classical.choice, Quot.sound`. All five output files (`Checks.lean`, `support.log`,
  `controls.log`, `types-axioms.log`, `receipt.json`) are **byte-identical** to the packet's
  `validation/`. Copies are in `rebuild-copy/`.
- Second, reviewer-written pipeline (`independent_run.py`): authenticates the anchor, recompiles the
  frozen sources in a fresh `/var/tmp` directory, then compiles `Independent.lean`. A kernel-side
  `run_cmd` there enumerates **every** constant of modules `T117Q` (39 total) and `Controls` (19)
  from the imported environment, including internal auxiliaries. It rejects any `axiom` or `unsafe` constant and any
  axiom outside the standard three in `collectAxioms`. All pass. The only non-internal constant
  beyond the 46 named ones is the auto-generated `T117Q.spectralCut.congr_simp`. No opaque
  constants are present. Logs and receipt are in `independent-logs/`.
- Printed types (`rebuild-copy/types-axioms.log`) were compared line by line against the sources
  and the claims below. The pretty-printer drops the parentheses in `h • ((∑ 1) - α • 1)`; the
  source is explicit and the reviewer instance `Qs_budget` elaborates the intended reading.

## 4. Semantic audit of the claims

| Claim | Finding |
|---|---|
| Arbitrary finite complex matrices, Loewner order | `n : Type*` with `[Fintype n] [DecidableEq n]`, entries `ℂ`, real scalars. `open scoped MatrixOrder`; `Matrix.le_iff : A ≤ B ↔ (B - A).PosSemidef` is `Iff.rfl`. Reviewer `swap_not_loewner_nonneg` shows the entrywise-nonnegative `[[0,1],[1,0]]` is **not** `≥ 0`, so the order is not entrywise. |
| `spectralCut` built from the Hermitian spectral theorem | Definition uses `hQ.posSemidef.isHermitian.eigenvectorUnitary` and `.eigenvalues`. `spectral_model` is exactly mathlib's `IsHermitian.spectral_theorem`. Nothing about P is assumed; the hypotheses are only `Q` and `0 ≤ Q`. |
| Positivity, idempotence, bounds; h(I−P) ≤ Q; PQP ≤ hP | `spectralCut_nonneg/le_one/idempotent/defect/compression`, proved through diagonal monotonicity under unitary conjugation. `defect` holds for every real h. Threshold is closed (≤ h): `cutoff_keeps_threshold`. |
| P(Z*Z)P ≤ hP under Z*Z ≤ Q | `spectralCut_domination`, for arbitrary complex `Z` (covers self-adjoint `Z_si` with `Z² = Z*Z`). It is not used downstream and is a standalone formal check of the §3 compression step before the norm conversion. |
| Finite-family budget gives half coverage | `spectral_half_coverage`: `∑ Q_s ≤ (h|s|/2) I`, `h > 0` ⇒ `(|s|/2) I ≤ ∑ P_s`, via general `selector_coverage` (arbitrary `P`, arbitrary finite `s`). |
| Positive Y, summed Re Tr pairing | `positive_trace_coverage` / `spectral_trace_bound`: `(|s|/2) Re Tr Y ≤ ∑ Re Tr(Y P_s)` for `0 ≤ Y`, through `trace_product_nonneg` (A = C*C plus cyclicity). |
| Nonempty family + per-chart b ⇒ Tr Y ≤ 2b | `trace_budget_consequence`. |
| No commutation assumed | No hypothesis in any of the 31 support types mentions products of selectors, inputs or `Y`. The reviewer controls instantiate the actual interfaces with noncommuting data (section 5). |

**Relevance to candidate §3.** The relevance checks out. With `S = |s|`, `Q_s = (∑_i Z_si^{2q})^{1/q}` and
`h = 8e q/m`, the candidate's displayed bound `S⁻¹ ∑ Q_s ≤ 4e q/m I` is exactly the Lean budget
`∑ Q_s ≤ (hS/2) I`. Here `P_s = 1_[0,h](Q_s)` is `spectralCut` (eigenvalues are nonnegative, so
`≤ h` equals `[0,h]`), `I − P_s ≤ Q_s/h` is `spectralCut_defect`, `∑ P_s ≥ S I/2` is
`spectral_half_coverage`, and `(S/2) Tr Y ≤ ∑ Tr(Y P_s)` is `spectral_trace_bound`. The per-chart bound
`Tr(Y P_s) ≤ N t √h + e` summed to `S N t √h + S e` is the `hb` input with `b = N t √h + e`.
`Tr Y ≤ 2b = 2√(8e)·N t √(q/m) + 2e` then matches (3.1)'s form. `Re Tr` agrees with `Tr` for
`Y ≥ 0`.

**Hidden conclusions.** None found. The inputs are `0 ≤ Q_s` and the budget (from (2.1),
operator concavity and Loewner–Heinz, which are unformalized), `0 ≤ Y` (from (3.2), unformalized), the per-chart `hb`
(trace duality, Bessel and `‖Z_si P_s‖ ≤ √h`, unformalized), and `Z*Z ≤ Q` for domination.
None of these restates coverage, the summed pairing or `Tr Y ≤ 2b`. `hb` bounds individual
`Re Tr(Y P_s)`, while the conclusion bounds `Re Tr Y`. Passing from one to the other is exactly the
coverage-plus-positivity step that is proved. The per-chart bound is genuinely an assumed input,
as the README states.

## 5. Controls

Packet controls (15) were checked for meaning:

- `p = diag(1,0)` and `r = ½[[1,1],[1,1]]` are self-adjoint idempotent rank-one projections, `≥ 0` in the Loewner order,
  and `pr ≠ rp`. `noncommuting_positive_pairing` only exercises `trace_product_nonneg`, not the
  selector, coverage or trace-bound interfaces. That is weak but correct.
- `positive_trace_hypothesis_necessary`: monotone pairing fails for `Y = −1`. This is meaningful for
  `trace_product_mono`.
- `positive_threshold_necessary` is an **abstract** single-chart instance (`Q = P = 0`, `h = 0`,
  `α = ½`). It refutes the defect-to-coverage implication of `selector_coverage` at `h = 0`. It is
  **not** a statement about `spectralCut`. The reviewer proves `spectralCut 0 _ 0 = I`
  (`spectralCut_zero_at_zero`) and that with the same data the genuine selector does cover
  (`genuine_zero_threshold_covers`). The README states this distinction correctly. Informally, the
  `0 < h` hypothesis is superfluous for `spectral_half_coverage` and its consequences: `h = 0` forces every `Q_s = 0`, hence
  `P_s = I`, and `h < 0` makes the budget infeasible for nonempty `s`. Only the `h = 0` instance is
  formalized here. This is harmless because the candidate uses `h > 0`.
- `nonempty_family_necessary` is purely arithmetic (`∀ b, vacuous → 1 ≤ 2b` is false). It does
  not instantiate `trace_budget_consequence`.
- `cutoff_keeps_threshold` / `cutoff_discards_strictly_above` correctly pin the closed threshold for
  every finite size and every unitary.

Reviewer controls (`Independent.lean`, 23 declarations, standard axioms, at the **actual**
interfaces):

- `noncommuting_selector_coverage` / `noncommuting_trace_coverage`: `selector_coverage` and
  `positive_trace_coverage` with selectors `(p, r, I, I)`, inputs `(I−p, I−r, 0, 0)`, `h = 1`,
  `α = 2`, and `Y = p`, which does not commute with selector `r`. Both selectors and inputs are proved
  noncommuting.
- `noncommuting_inputs_trace_budget`: all hypotheses of `trace_budget_consequence` are jointly
  satisfiable with noncommuting `Q`'s and `Y = p`. This is non-vacuity only. With `h = 1` these genuine selectors
  are `I`, so their noncommutation is not claimed.
- `abstract_zero_threshold_interface`: the packet's h = 0 counterexample restated literally in
  `selector_coverage`'s Finset form.
- `positivity_needed_actual_interface`: `positive_trace_coverage`'s coverage hypothesis holds and
  its conclusion fails for `Y = −1`.
- `empty_family_actual_interface`: every hypothesis of `trace_budget_consequence` except
  `s.Nonempty` holds (`s = ∅`, `Q = 0`, `h = 1`, `Y = I`, `b = 0`), and the conclusion fails.
- `order_is_loewner`, `swap_entrywise_nonneg`, `swap_not_loewner_nonneg`: order semantics.

## 6. Exact limits

- Scoped support only. Unformalized: Gaussian/Wick moments (Lemma 1); the universal empirical
  design (2.1); fractional powers, operator concavity and Loewner–Heinz that produce `Q_s`, the input budget and
  `Z_si² ≤ Q_s`; conversion of `P Z² P ≤ hP` to `‖Z P‖ ≤ √h`; the Gaussian sign and Bessel construction of `X_j`
  and `Y` with `Y ≥ 0` and `Tr Y = E‖A(g)‖₁`; trace-norm duality and the per-chart bound `b`; every
  source metric, coarea, smoothing, copy, asymptotic and infinite-dimensional step (§§4–7).
  No full T117Q theorem, metric or distortion statement is represented in Lean. No numerical
  proof is claimed.
- `spectralCut` is defined through mathlib's chosen eigenbasis. Its independence from that choice
  (uniqueness of the spectral projection, or agreement with `cfc`) is not stated. §3 uses only the
  five proved properties, so this is not needed.
- Trust: the Lean kernel and compiler, and the pinned dependency object cache
  (`formal/.lake/packages`), which was **not** rebuilt from source. Pins and tracked cleanliness
  were checked, but `.olean` object integrity is trusted. No network was used.
- The reviewer's informal remark that `0 < h` is superfluous is not formalized beyond `h = 0`, `Q = 0`.

## 7. Optional improvements (non-blocking)

1. Move a noncommuting-selector instance of `selector_coverage` / `positive_trace_coverage` into
   `Controls.lean` (as in `Independent.lean`). The current p/r control only exercises
   `trace_product_nonneg`.
2. Restate `positive_threshold_necessary` and `nonempty_family_necessary` literally at the
   `selector_coverage` / `trace_budget_consequence` interfaces.
3. Optionally drop `0 < h` from `spectral_half_coverage` and its consequences, or note that it is
   superfluous there. It is needed only for the abstract `selector_coverage`.
4. Optionally add a lemma identifying `spectralCut` with the `cfc` indicator projection, to remove
   the eigenbasis-choice caveat.
5. Note in the README that the pretty-printed budget type omits parentheses.

## 8. Files

Review membership is sealed in `review-manifest.json`, whose SHA256 is reported externally.
Verify it with `python3 -B verify.py --anchor <SHA256>`. `seal_controls.py` runs copied mutation controls
on `/var/tmp` copies only.
