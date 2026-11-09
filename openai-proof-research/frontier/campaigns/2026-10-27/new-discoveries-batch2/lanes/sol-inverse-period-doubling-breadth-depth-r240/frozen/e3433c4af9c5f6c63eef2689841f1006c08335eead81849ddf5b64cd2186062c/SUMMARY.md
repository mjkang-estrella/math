# Pendulum convex moments and interior series: completed component

All assigned mathematical obligations are closed without additional analytic premises. Credit 0. Counts stay 9 additional / 39 total, next 40. This is an interior formal component, not acceptance or a proof of the closed-interval SourceClaim.

## Exact interfaces

All names are in namespace PendulumTimeMap; a,z,phi are real, n is natural.
The four inherited modules Defs, Substitution, Moments, Source are byte-identical to sol-pendulum-source-moments-formal-r1. Their literal interval-integral definitions are used throughout.

```lean
weight (n : ℕ) : ℝ := (Nat.choose (2*n) n : ℝ) / 8^n

weight_pos (n : ℕ) : 0 < weight n

moment_convex (n : ℕ) {a : ℝ} (ha : 0<a) :
 ConvexOn ℝ (Ioi 0) (moment n a)

weight_hasSum {t : ℝ} (ht : |t|<2) :
 HasSum (fun n => weight n*t^n) ((1-t/2)^(-1/2:ℝ))

transformedTime_hasSum {a z : ℝ}
 (ha : 0<a) (ha2 : a<2) (hz : 0<z) (hz2 : z<2) :
 HasSum (fun n => weight n*moment n a z)
  (2*Real.sqrt 2*transformedTime a z)

moment_series_summable {a z : ℝ}
 (ha : 0<a) (ha2 : a<2) (hz : 0<z) (hz2 : z<2) :
 Summable (fun n => weight n*moment n a z)

transformedTime_series {a z : ℝ}
 (ha : 0<a) (ha2 : a<2) (hz : 0<z) (hz2 : z<2) :
 transformedTime a z =
  (1/(2*Real.sqrt 2))*∑' n, weight n*moment n a z

transformedTime_convex {a : ℝ} (ha : 0<a) (ha2 : a<2) :
 ConvexOn ℝ (Ioo 0 2) (transformedTime a)

sourceTime_interior_convex {phi : ℝ}
 (hp : 0<phi) (hp2 : phi<Real.pi/2) :
 ConvexOn ℝ (Ioo 0 2) (sourceTime phi)
```

These are actual compiled statements, not proposed interfaces. See formal/Convexity.lean and formal/Series.lean for all helper interfaces and actual-declarations.json for fully elaborated actual types including private/generated declarations.

## Moment proof

moment_zero_convex and moment_one_convex use the inherited combined exact identities M0=pi and M1=pi(a+z)/2-2sqrt(a*z). The latter uses concavity of sqrt. No separate low-order moving-piece convexity is asserted.

For all n the fixed integral is convex. Pointwise inverse-square-root Jensen follows by composing sqrt concavity with reciprocal convexity on positive inputs. It is integrated on the open interval using inherited all-n moment integrability, discarding only null endpoints.

For n>=2, movingKernel n a z y is literally
(max (z-y) 0)^((n:Real)-1/2)/sqrt(a+y).
positivePart_rpow_convex proves convexity for every real exponent >=1. momentKernel_rpow proves the natural-power/square-root equality for n>=1, including t=0, rather than assuming agreement of totalized expressions. movingKernel_eq_momentKernel and moving_integral_truncated prove the reflected substitution y=z-t and equality with a finite-support integral on any common bound L>=z. movingKernel_continuousOn proves the needed integrability on [0,L]. Jensen uses L=max x (max y (u*x+v*y)), so all three evaluations share a single finite support. This closes moving_integral_convex and then moment_convex for every n and every a>0.

## Binomial identity and exchange

choose_step proves the generalized-binomial recurrence from the Pochhammer definition. weight_step uses the natural central-binomial recurrence. Induction gives exactly
weight n = Ring.choose (-1/2) n * (-1/2)^n.
The actual mathlib binomial power-series theorem at -t/2, |t|<2, gives weight_hasSum. No finite coefficient controls substitute for the infinite identity.

kernel_hasSum multiplies that HasSum by the literal reciprocal sqrt(t*(a+z-t)) and proves the square-root algebra giving sqrt(2)*transformedKernel. series_piece applies intervalIntegral.hasSum_integral_of_dominated_convergence, with the nonnegative summands themselves as bounds. Pointwise summability is the just-proved kernel identity; integrability of their tsum follows by equality almost everywhere with the inherited integrable transformed kernel. The inherited moment integrabilities establish every summand's measurability. Thus exchange does not assume summability of the integrated series or the intended final identity. Applying it at r=a and r=z proves transformedTime_hasSum, hence actual summability and the requested normalization.

The final Jensen inequality compares the genuine HasSum limits using hasSum_le and moment_convex with strictly positive weights. It then uses the inherited literal sourceTime_eq_transformedTime. There are no open series assumptions in sourceTime_interior_convex.

## Audit, provenance and replay

Six mathematical modules, 96 actual origin declarations (46 inherited, 50 new), including private/generated helpers. FullAudit inventories all actual module-origin declarations and independently cross-checks moduleData.constNames; it prints actual kernel types, transitive axioms, and safety/partial/axiom flags. All declarations use only propext, Classical.choice and Quot.sound, and all forbidden flags are false. Mathematical source scan excludes sorry/admit/axiom/unsafe/native_decide/partial/implemented_by. dependency-hashes.json hashes 15009 actual imported upstream compiled dependency files, including companion/private/server parts where present.

Compiler SHA256 e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550; mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 and eight companion revisions verified. pins.json, guard.py, helper_guard.py and replay_guard.py are unchanged predecessor bytes. Predecessor source-only archive SHA256 equals root's supplied 05cef5c6617e1372f925340e70d5f4c5444afe2844840eb0fbc8ac902bd5fcb0. No own compiled input was copied.

freeze-before.json and freeze-after.json verify the same moments-adoption freeze and all 121 payload records. verify_inputs.py additionally verifies 532 inherited/frozen-original records and every selected original/copy input. Original ordinary proof, adjudication/reviews and independent endpoint supplement are included as evidence, not altered.

component-source.zip is deterministic and source-only; component-source-repeat.zip has identical bytes. Fresh EXTRACTED replay starts without own compiled artifacts, verifies pins/inputs/manifests and actual upstream dependency hashes, serially compiles all six mathematical modules plus FullAudit, and compares actual audit rows and dependency hashes with the archived expected results. replay-receipt.json and FINAL-RECEIPT.json record the outcome; no full SourceClaim PASS is asserted.

Lean caps: unchanged guard, serial -j1, -M2700, warningAsError=true, autoImplicit=false; groupRSS2800MiB sampled nominal45ms, CPU210s, wall230s. Helpers use the requested unchanged designated helper_guard, fixed AS/groupRSS512MiB, CPU210s, wall230s and requested environment. Sampling cannot exclude unsampled transients; no cap raises.

Process qualification: the initial pwd, ls and bootstrap read of helper_guard were unguarded before the guard interface was known. This violates a literal all-command requirement and is explicitly retained in PROVENANCE.json; no claim of flawless process compliance is made. All subsequent helper/search/edit/hash/check operations used the designated guard. Failed Lean source snapshots/logs/guard receipts are retained under attempts/. A nonexistent binomial source-path search and truncated broad displays are retained in the tool transcript; no mathematical or absence claim depends on them. No network/browser, child agents, external messages/uploads, git, shared/count/public mutations occurred. Writes stayed inside this assigned lane.

## Residuals and integration

No assigned interior obligation remains. Root can consume sourceTime_interior_convex directly as the premise of the separately assigned sourceClaim_of_interior_convex. Literal endpoint continuity, endpoint integrability and closed transfer are not proved or duplicated here. SourceClaim on Icc 0 2 remains unproved by this component. No C2, strictness or quantitative curvature claim is made. Historical acceptance coverage gaps, final independent review, paper and acceptance remain root responsibilities. Credit stays 0.
