# Pendulum source and exceptional moments: completed finite component

All mandatory component obligations are proved in four mathematical Lean modules. **The full SourceClaim is defined, not proved. Credit 0; counts remain 9 additional / 39 total, next 40.** No acceptance or full-published-claim formal PASS is asserted. No manuscript or optional endpoint-continuity theorem was attempted.

## Literal definitions and stable interfaces

Namespace `PendulumTimeMap`; all parameters below are real unless `n : ℕ`. Definitions in `formal/Defs.lean` are exposed and denote real interval integrals with Lebesgue volume:

```
b z = Real.arccos (1-z)/2
a phi = 1-Real.cos (2*phi)
sourceKernel phi z x = (Real.sqrt (z-Real.cos (2*phi)+Real.cos (2*x)))⁻¹
sourceTime phi z = (∫ x in 0..phi, sourceKernel phi z x)
                 + (∫ x in 0..b z, sourceKernel phi z x)
transformedKernel a z t = (Real.sqrt (t*(2-t)*(a+z-t)))⁻¹
transformedTime a z = (1/2)*((∫ t in 0..a, transformedKernel a z t)
                          +(∫ t in 0..z, transformedKernel a z t))
momentKernel n a z t = t^n / Real.sqrt (t*(a+z-t))
moment n a z = (∫ t in 0..a, momentKernel n a z t)
              +(∫ t in 0..z, momentKernel n a z t)
SourceClaim = ∀ phi : ℝ, 0<phi → phi<Real.pi/2 →
  ConvexOn ℝ (Set.Icc 0 2) (sourceTime phi)
```

The following are actual proved types, with no additional analytic premise:

```lean
a_range {phi : ℝ} (h0 : 0<phi) (h1 : phi<Real.pi/2) :
  0<a phi ∧ a phi<2
b_range {z : ℝ} (h0 : 0<z) (h1 : z<2) :
  0<b z ∧ b z<Real.pi/2
a_b {z : ℝ} (h0 : 0≤z) (h1 : z≤2) : a (b z)=z

moment_integrable (n : ℕ) {a z : ℝ} (ha : 0<a) (hz : 0<z) :
  IntervalIntegrable (momentKernel n a z) volume 0 a ∧
  IntervalIntegrable (momentKernel n a z) volume 0 z
moment_zero {a z : ℝ} (ha : 0<a) (hz : 0<z) : moment 0 a z=Real.pi
moment_one {a z : ℝ} (ha : 0<a) (hz : 0<z) :
  moment 1 a z=Real.pi*(a+z)/2-2*Real.sqrt (a*z)

source_integrable {phi z : ℝ} (hp : 0<phi) (hp1 : phi<Real.pi/2)
  (hz : 0<z) (hz1 : z<2) :
  IntervalIntegrable (sourceKernel phi z) volume 0 phi ∧
  IntervalIntegrable (sourceKernel phi z) volume 0 (b z)
transformed_integrable {a z : ℝ} (ha : 0<a) (ha1 : a<2)
  (hz : 0<z) (hz1 : z<2) :
  IntervalIntegrable (transformedKernel a z) volume 0 a ∧
  IntervalIntegrable (transformedKernel a z) volume 0 z
sourceTime_eq_transformedTime {phi z : ℝ} (hp : 0<phi) (hp1 : phi<Real.pi/2)
  (hz : 0<z) (hz1 : z<2) : sourceTime phi z=transformedTime (a phi) z
```

Moment theorems are stronger than the requested interior rectangle: positivity alone suffices. Other reusable interfaces, including their full actual elaborated types, are in `actual-declarations.json` and `formal/Substitution.lean`, `formal/Moments.lean`, `formal/Source.lean`.

## Proof scope

`change c x = c/2*(1-cos(2*x))`. `weighted_substitution` proves integrability and the identity

```
∫ t in 0..change c q, w t / sqrt(t*(c-t))
  = 2 * ∫ x in 0..q, w (change c x)
```

for `0<c`, `0<q<pi/2`, and `ContinuousOn w (Icc 0 (change c q))`. The proof uses mathlib's genuine monotone change-of-variables theorem and its integrability equivalence. The derivative is nonnegative, the square-root cancellation is proved on the open interval, and interval-integrability/integral congruence discards only the null endpoints. It never infers integrability merely from a totalized integral identity.

For moments choose `c=a+z` and `q=angle c r=b(2*r/c)` for each cutoff `r=a,z`. Polynomial weights are continuous for every natural exponent. Complementarity follows from `arccos(-u)=pi-arccos(u)`. Integration of the constant and cosine gives the exact zeroth and first moments; `change_sqrt` proves the sine boundary terms equal `sqrt(a*z)`. For the source choose `c=2` and `w(t)=1/sqrt(a(phi)+z-t)`; strict positivity of its argument on each closed cutoff interval proves continuity and both original integrabilities. Thus the literal journal substitution, its endpoint behavior, and its singular transformed integrals are genuinely certified.

Remaining later-component types are `SourceClaim` itself, higher-moment convexity, the binomial/MCT identity, and closed-endpoint continuous-extension assembly. None is assumed, stubbed, or conditionally certified here. No C2 or strict-convexity assertion is made.

## Provenance, checks, and replay

Scientific inputs: candidate57 freeze and ordinary `PROOF.md`, both specified reviews, root DECISION/INTERFACE and root354-review freeze, copied into `inputs/`. Original frozen entries were verified before scientific implementation; 411 entries total (57+354). `originals-before.json` preserves expected hashes; `input-records.json` records every selected copy and unchanged infrastructure file. Root context ledger/prior-context/NEXT was read; no shared file changed. No new source or registry research occurred.

The compiler SHA256 is `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`. Mathlib revision is `d13f23b723b8a846827a245b89c10fc7d3f11612`. `pins.json` is unchanged from the established lane. It contains nine package records: mathlib plus eight companion packages; all nine revisions are verified by reading repository metadata, without git commands. Guard/helper/replay-guard bytes are unchanged. Only audit/replay/packaging logic is adapted; no unrelated mathematical lemma or build output was copied.

`FullAudit` imports all bodies from all four mathematical modules. It inventories every actual origin declaration, including generated private simp helpers, proof helpers and equation declarations, and checks module-data coverage. All 46 actual declarations have transitive axioms contained in `{propext, Classical.choice, Quot.sound}` and unsafe/partial/axiom flags false. `actual-declarations.json` contains every full elaborated type and origin. `dependency-hashes.json` hashes the actual imported upstream olean dependency set, including present `.private` and `.server` companions, for packages and compiler libraries.

Run from this lane, with the environment variables shown:

```sh
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python replay_guard.py python replay.py component-source.zip EXTRACTED-new
```

The destination must not exist. The deterministic archive has no own compiled artifacts. Replay verifies manifest, pins, original inputs and upstream dependency hashes, compiles serially from extracted sources, audits every actual declaration, compares full type/axiom/flag reports and dependency sets, and verifies the source manifest again. `EXTRACTED/replay-receipt.json` is the fresh delivered receipt; `archive-receipt.json` records determinism and archive SHA256. Packaging makes two byte-identical archives.

Every Lean compile, including failed attempts and the audit, uses the unchanged supervisor: j1, M2700, warningAsError, autoImplicit=false, group RSS2800MiB, CPU210s, wall230s, nominal45ms. Helper work uses the designated unchanged 512MiB AS/group-RSS helper guard, CPU210s, wall230s, nominal40ms. RSS is sampled, so unsampled transient excesses are not excluded. No caps were raised. Local `attempts/` preserves successive logs/source snapshots; early failures involved noncomputable marking, module exposure/import syntax, theorem namespace/implicit arguments, and proof elaboration. An initial audit attempt before Source compiled failed on the absent own module. All were corrected; no proof holes or analytic oracles were added. The first failed Defs log predates its snapshot's noncomputable edit; the original patch and full diagnostic are also in the tool transcript. No failures were deleted. Native bounded reads and apply_patch were used as authorized; all Python helper/edit/hash/package work was supervised. The replay itself uses the unchanged replay guard and each nested compile its own unchanged Lean guard.

No child, git operation, shared-file/package mutation, external post/message/upload/browser, or manuscript. This component receives no discovery credit.
