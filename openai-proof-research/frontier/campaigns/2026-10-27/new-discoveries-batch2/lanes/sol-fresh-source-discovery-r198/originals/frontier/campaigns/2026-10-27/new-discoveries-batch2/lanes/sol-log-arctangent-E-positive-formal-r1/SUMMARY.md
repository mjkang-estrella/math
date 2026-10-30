# Literal E positivity — formal component

Status: closed Lean E-component; final source-only replay receipt and provenance
are in this lane. Formal investment only. Candidate credit 0; campaign remains
3/30 additional, 33/60 total. No source-conjecture or discovery acceptance claim.

## Exact integration interface

Import `MeanEPositive`. Namespace `LogArctangentMean` exports

    E_pos {t : ℝ} (ht : 0 < t) : 0 < E t

Here `d = Real.sqrt 17` and `A, B, U, V, E` are the literal total real
functions requested, in MeanAnalyticDefs.lean. In particular U contains
`deriv B t * A t - B t * deriv A t - A t ^ 2`. No unexplained coefficient,
derivative-chain, interval, smoothness or jet premise occurs in E_pos.
`Ap` and `Bp` are explicit derivative functions, not power means.

Supporting integration endpoints:

* `d_sq`, `d_bounds`: d²=17 and 41/10<d<21/5.
* `hasDerivAt_A/B`, `deriv_A/B`, `contDiff_A/B/U/V/E`.
* `U_expansion`, `V_expansion`: actual finite exponential tables
  `UExpansion`, `VExpansion`, including constant U coefficient −87/68.
* `freq0,…,freq11`, `u0,…,u11`, `v0,…,v11`: explicit coefficients
  in the descending positive-frequency order
  7+d, 2+2d, 10, 5+d, 2d, 8, 3+d, −2+2d, 7−d, 2, −3+d, 5−d.
  `frequencies_ordered` proves all adjacent comparisons and positivity.
* `c0_0,…,c11_2`: literal coefficient formulas with 1104,94,2.
  `prefix_value_i_j` and `prefix_pos_i_j`, i=0,…,11, j=0,1,2,
  prove all 36 exact values and signs in the kernel.
* `E_eq_evalExpList`: connects E to the explicit genuine exponential list.
  `ExpQuadratic.hasDerivAt`, `iteratedDeriv_evalExpList`,
  `ExpQuadratic.jet_formula` prove the derivative machinery.
* `E_derivative24 (t)`: the exact requested iteratedDeriv24/2 formula,
  unrolled over 12 frequencies. Its linear term is c1+c2, hence 96u.
  The constant-frequency quadratic is retained until differentiation kills it.
* `E_derivative24_pos (ht : 0 ≤ t)`.
* `E_initial_jets (hn : n < 24)`: zero except exactly 10,12,…,22,
  with values 37847040;19891322880;5550283554816;1162696473968640;
  206947471161556992;33226670114812723200;4978839848478924865536.
* `derivative_ladder`: continuous actual iterated derivatives, nonnegative
  jets and positive top derivative imply positivity on t>0 by descending
  strict monotonicity on [0,∞), including comparison to the actual value at 0.
* Import `FiniteAbel` separately for the generic finite identity and
  `finiteAbel_nonneg/pos`. The concrete weighted proofs use the same finite
  Abel decomposition unrolled and proved by ring, with all signed prefixes.
  Individual coefficient positivity is never assumed.

The kernel checks arithmetic identities and rational interval bounds; JSON is
only a transcription source. It is not trusted as an axiom. No infinite series,
numerical sampling or external polynomial checker supplies a proof premise.

## Scope and remaining work

No mathematical gap remains in this E component. The actual source Conjecture37
endpoint, A/B positivity and scaled zero limits, arctangent comparison, logarithmic
gap, the Stolarsky stabilization for both signs, power-mean sandwich and
homogeneous transfer remain root integration work. No SourceClaim is introduced.
No novelty or public-proof-registry clearance is newly asserted in this lane.
The supplied ordinary proofs/reviews and adopted INVEST decision are provenance,
not axioms or replacements for kernel proofs.

## Audit and replay

Fresh replay PASS: 38 modules (28 mathematical/support/assembly modules plus
Inventory and nine audit modules), 409 declarations, 103.95 seconds total;
sampled peak process-tree RSS 3,103,628KiB < 3GiB. Receipt SHA256
7eb8532971e9b45f7ee5586d0ac146321ef7f69e00b4b14c5cc67aaf9b203060.

All 409 namespace-origin environment names were inventoried, including compiler
generated equations, recursors, match functions, numeral and simplifier helpers.
Audit0–Audit8 print every actual type and `#print axioms` result. I personally
read all nine complete reports, using namespace-prefix abbreviation only for
display. Every result uses only propext, Classical.choice, Quot.sound (or fewer).
All exported theorem hypotheses and endpoints were checked against the literal
definitions. Source scans found none of the prohibited proof escape tokens.

`replay/` started with only copied .lean sources and the byte-identical
root-cascade runner, no inherited .oleans for any lane module. Its LEAN_PATH is
only that fresh cwd plus the pinned package build paths. Modules are compiled
serially, with autoImplicit=false, warningAsError=true, -j1, 110 CPU seconds and
120 wall seconds per invocation, and 20ms process-tree RSS sampling with a
3GiB stop threshold. See replay/receipt.json and replay/logs for all commands,
exit codes, hashes and resource samples. Audit-only auxiliary-name lints are
disabled intentionally to inspect every generated declaration. A few generated
arithmetic files disable unused-simp/tactic style lints; proof and compiler
warnings still use warningAsError.

Reproduce by running `python3 replay.py` after moving the existing replay
directory aside within this lane; the script deliberately refuses to reuse an
existing directory. It copies only sources and compiles in dependency order.
The authoritative deliverable is formal/*.lean. Construction scripts are
retained; `regenerate.py` recreates mathematical generated files, including the
high-jet memory optimization. Audit sources are generated after Inventory.

`dependency-hashes.json` hashes the recursive resolved import closure's source
and compiled dependency files. Compiler SHA256 is independently checked against
the requested value in input-check.json. The mathlib revision label is the
user-supplied d13f23b723b8a846827a245b89c10fc7d3f11612; no git operation was used to
authenticate ancestry. Input-before/after.json and input-check.json verify frozen
inputs and the six certificate-freeze hashes unchanged. The exact diagnostic/
hash scripts enforce 512MiB AS, 35 CPU seconds, 45-second shell deadlines and
single-thread environment settings.

## Resource diagnosis and procedural limits

Preliminary blanket Mathlib imports were unsuitable: before the RSS watchdog
was installed, one preliminary run reported 6,909,804KiB child peakRSS and
another broad tactic import 3,516,600KiB. These are failed exploratory resource
runs, not compliant certificate receipts; this deviation is disclosed.
An initially self-imposed 3GiB *virtual address* cap caused thread-creation
failure, so the implementation was corrected to the requested RSS metric.
No final RSS ceiling or CPU deadline was raised.

Under the watchdog, an overexpanded E equality, a grouped high-jet file, jet21
and an unnecessary full Lean audit import were stopped at the 3GiB boundary.
Fixes: specific imports, normalize exponential coordinates before ring
expansion, split large jets into single-declaration modules, cancel odd jets
before radical expansion, and reuse already available command APIs.
The final sources replay under the original RSS limit. Earlier algebra,
style-linter and simplification-depth failures were resolved in source.
Exploratory Probe text and failed logs are retained separately; no exported
proof depends on them. A shell rm-f cleanup was rejected by the tool policy;
the diagnostic source was instead retained by a lane-local rename.

No children, git operations, other-lane edits, browser tabs, network requests,
publication/contact/account actions, or ledger changes occurred.
