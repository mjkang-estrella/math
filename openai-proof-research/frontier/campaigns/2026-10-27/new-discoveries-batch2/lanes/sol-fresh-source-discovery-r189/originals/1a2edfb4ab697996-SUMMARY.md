# Generic one-crossing component — formal PASS, credit 0, novelty HOLD

This lane implements the independent generic comparison component requested by root. It does **not** claim a literal Gamma/Bessel theorem, source-level formal completion, novelty clearance, acceptance, or new comparison machinery. Root decides acceptance. No files from the changing parallel series lane were read. No children, git operations, shared edits, network access, or external actions occurred. All writes are confined to this lane.

## Exact interfaces

Namespace: `BesselTransfer`. All functions below have type `ℝ → ℝ`; A and B are arbitrary real numbers except for the displayed hypotheses. All derivative hypotheses apply only at x>0 and use ordinary `HasDerivAt`.

The three shape definitions in `formal/Crossing.lean` are exactly:

```lean
InitiallyPositive W :=
  ∀ x : ℝ, 0 < x → ∃ z : ℝ, 0 < z ∧ z < x ∧ 0 < W z

IncreasingOrPeak R :=
  StrictMonoOn R (Ioi 0) ∨ ∃ c : ℝ, 0 < c ∧
    StrictMonoOn R (Ioc 0 c) ∧ StrictAntiOn R (Ici c)

Unimodal R :=
  MonotoneOn R (Ioi 0) ∨ AntitoneOn R (Ioi 0) ∨
    ∃ c : ℝ, 0 < c ∧ MonotoneOn R (Ioc 0 c) ∧ AntitoneOn R (Ici c)
```

This `Unimodal` is a sufficient stronger shape for the published definition: it includes monotone/constant functions and a single peak, while the source also permits a valley. It does not assert equivalence with a separately formalized source definition. The peak intervals contain c, so the strict alternative gives a genuine unique maximum throughout the positive half-line.

The main generic source-facing endpoint, `unimodal_transfer` in `formal/Transfer.lean`, has this exact interface:

```lean
theorem unimodal_transfer {R W p D : ℝ → ℝ} {A B : ℝ}
    (hB : 0 ≤ B) (hp : ∀ x > 0, 0 < p x)
    (hw : ∀ x > 0, HasDerivAt W ((A/x-B*x)*p x) x)
    (hinit : InitiallyPositive W ∨
      (A ≤ 0 ∧ Tendsto W (𝓝[>] 0) (𝓝 0)))
    (hD : ∀ x > 0, 0 < D x)
    (hr : ∀ x > 0, HasDerivAt R (W x / D x) x) :
    Unimodal R
```

The stronger `initial_transfer` replaces `hinit` by `hi : InitiallyPositive W` and concludes `IncreasingOrPeak R`, with **no restriction on A**. `initial_of_eventually` converts eventual positivity in `𝓝[>] 0` to `InitiallyPositive`. The latter only asks for positive values arbitrarily close to zero; it does not require W to have any finite endpoint value. This accommodates divergent positive W when the source order sum is negative.

The closed sign theorem `sign_dichotomy` uses just hB, hp, hw, and hi and concludes exactly:

```lean
(∀ x > 0, 0 < W x) ∨ ∃ c : ℝ, 0 < c ∧ W c = 0 ∧
  (∀ x, 0 < x → x < c → 0 < W x) ∧
  (∀ x, c < x → W x < 0)
```

`unique_zero` in `formal/Cases.lean` proves that any two positive zeros coincide, under the same four hypotheses. No existence of a zero or peak is assumed or asserted in every case. The second branch is constructed by the intermediate value theorem only after failure of strict positivity everywhere. The derivative-to-ratio transfer then proves both strict monotonicity claims.

The other endpoints are:

* `zero_limit_transfer`: hA : A≤0, hB, hp, hw, right zero limit, hD and hr imply `AntitoneOn R (Ioi 0)`.
* `strict_zero_limit_transfer`: the same hypotheses plus `A < 0 ∨ 0 < B` imply `StrictAntiOn R (Ioi 0)`.
* `equal_scale_increasing`: A≥0, hp, `HasDerivAt W ((A/x-0*x)*p x) x`, hi, hD and hr imply `StrictMonoOn R (Ioi 0)`; this includes A=0.
* `constant_zero_limit_transfer`: `HasDerivAt W 0 x` for every x>0, a right zero limit, and hr imply `∀ x>0, ∀ y>0, R x=R y`. No denominator positivity is needed here because W is identically zero. When A=B=0 the W derivative premise simplifies to this premise.

All exact elaborated types, including implicit binders and generated auxiliaries, are recorded in `verification-fresh/logs/OriginAudit.log` and as structured declaration rows in `verification-fresh/replay-receipt.json`.

## Case coverage and proof mechanism

With initial positivity, `initial_transfer` covers A≤0 or A>0, and B=0 or B>0 uniformly. Equal scales with A≥0 give strict increase by the specialized endpoint. Equal scales with A<0 retain the possible peak, as required by the negative-order stress case in the review. With a zero limit and A≤0, strict decrease holds whenever A<0 or B>0; A=B=0 gives constancy. The zero-limit endpoint does not claim coverage for A>0 without initial positivity; that combination is unnecessary for the ordinary proof's equal-order branch.

For B≥0, the coefficient A/x−Bx being nonnegative at x forces it nonnegative at every smaller positive argument. MVT and an initial positive value therefore force W(x)>0. Consequently W(x)≤0 forces a strictly negative coefficient at x, which stays strictly negative at every larger argument. Thus W strictly decreases after any nonpositive value. Continuity and initial positivity close the unique-zero alternative. There is no division by B, square-root threshold, large-x assumption, or silently assumed peak existence.

For the zero-limit branch, MVT gives antitonicity of W. Taking the right limit shows W≤0 everywhere. Strict negative derivative gives W(x)<W(x/2)≤0; a zero derivative gives W≡0. MVT transfers these signs through the supplied positive denominator.

## Provenance and remaining literal gaps

Read ancestor and batch AGENTS, batch ledger/prior-campaign context, upstream pin/catalogue opening, r57 `discovery.md`, eligibility `review.md`, and root `ADJUDICATION.json`. `provenance.json` binds copies of the three requested inputs, instructions, toolchain/manifest, and reused finalized-lane guard by before/copy/after hashes at packaging time. This freezing occurred after initial reading; no stronger pre-read freeze claim is made. No primary manuscript was independently fetched or reread here, and no fresh literature/registry search was attempted in this generic implementation lane.

The literal instantiation suggested by those supplied records remains openly unproved here:

```
f(x)=I_u(ax), g(x)=I_v(bx), R=f/g,
W=x(f'g−fg'), p=fg, D=x*g²,
A=u²−v², B=b²−a².
```

Root/series integration must supply the actual defining Gamma/Bessel series, positivity of p and D, differentiability and the scaled equations needed for hw/hr, eventual W positivity for u>v (including divergent W), and the zero limit when u=v. It must also connect the generic shape predicate to the chosen literal source endpoint and parameter quantifiers. Generic premises have not been renamed into completed literal facts. The ordinary proof supplies the intended case split; this component verifies its generic transfer only. The routine-classical-adaptation objection and current-registry/novelty HOLD remain unchanged.

## Replay, audits, limits, and receipts

Pinned Lean **4.34.1**, binary SHA256 `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`; Mathlib **d13f23b723b8a846827a245b89c10fc7d3f11612** from the requested 2026-10-14 formal cache. All nine package revisions are verified by reading metadata without git commands. `pins.json` and 18,160 dependency-file hashes bind imported source/build artifacts, including available private/server oleans and IR. No local package changes or builds were made.

`one-crossing-source.zip` contains sources, audit code, guarded runner, replay script, pins, input copies and manifests; no own prebuilt artifacts. `verification-fresh` was a newly created source-only extraction. Its search path contains only its own freshly built modules plus pinned cached dependencies. Fresh replay passed in serial module order Crossing, Transfer, Cases, OriginAudit. No warning suppression or cap increase was used.

The audit enumerates declarations by **actual environment module origin**, crosschecks against each module's complete constant inventory, prints actual fully elaborated types, collects transitive axioms, and rejects unsafe/partial/axiom flags on every own declaration. It also traverses the full type/value dependency closure and rejects unsafe/partial constants or nonallowed axioms there. Result: **31 own declarations**, **17,360 dependency constants**, axiom union exactly **propext, Classical.choice, Quot.sound**. All own safety flags false; proof sources contain no sorry/admit/axiom/unsafe/native_decide/implemented_by. Audit metaprogramming only inspects the completed proof environment; it introduces no theorem or assumption.

Fresh Lean commands use `-j1 -M2700 -DwarningAsError=true -DautoImplicit=false`. Each Lean process has CPU210s, wall230s, sampled process-group RSS2800MiB every45ms. Fresh peaks: Crossing 2,665,728KiB; Transfer 2,645,144KiB; Cases 2,659,260KiB; OriginAudit 2,659,540KiB. Each completed in under10 seconds. Sampling cannot rule out intersample transients. Guard/replay/package Python use AS512MiB and CPU210s with wall alarms230s; BLAS thread variables are1. The reused guard was adapted only to tighten its own Python alarm from240 to230 seconds. Trivial initial text-edit Python invocations preceded adding explicit per-script resource setup; they launched no Lean or numerical work. All substantive checking/packaging/replay used the bounded runners.

One development audit with broad `import Lean` was killed at sampled RSS2,876,380KiB (exit−9, ~1.04s). Broad audit imports were replaced by the specific Lean inspection modules; the final narrower audit and fresh replay pass below the same ceiling. No limits were raised. Earlier development syntax/linter failures were corrected before the fresh replay. `development-events.json` records the resource stop; final strict build/replay receipts are in both log directories and `verification-fresh/replay-receipt.json`.

To reproduce from this directory with a new destination:

```sh
python3 replay.py one-crossing-source.zip verification-another-fresh
```

Use a nonexistent destination inside this lane. `package.py` rebuilds the source-only archive and dependency manifest if integration changes are intentionally made. No acceptance/count files are touched.
