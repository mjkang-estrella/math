# Independent review of the kinetic Lean support

**Verdict: PASS for the nine advertised supporting algebra statements. No repair is required.** This is a semantic and fresh-compilation review of the frozen package, not a formal verification or renewed proof review of the full kinetic theorem, a novelty decision, or acceptance/count credit.

The authenticated author source is `../kinetic-formal-v1/KineticSupport.lean`, SHA256 `f4a419f9af0c2db04a54ac35f4ffcdebdd2db6aa1b246a5444c635357e735629`. Its `outputs.json` manifest has SHA256 `e859674105795b9ef811ff35e4c6587f047f1a4705ecf1f4fa58c625fb2faf3b`. All twelve manifest entries were verified before and after the independent run. The author source, metadata, and logs were not modified. See `provenance.json` for complete input authentication and exact read extents, `coverage.md` for each formal statement and its prose use, and `outputs.json` for hashes of this review's artifacts.

## What was checked independently

I read the entire source, README, original checks, verifier, package manifests, original validation and compiler logs. I read the repaired candidate's exact target, Lemma W physical chart and affine-origin/covariance definitions, and the transfer/chaining exponent passages. I checked the collision formula against the actual pinned primary manuscript, §03 `eq:atom-C` and `eq:atom-O`, not merely the catalogue or the prior PASS label. The source blob matches the immutable preprint tree. Upstream theorem truth is stipulated; this audit checks only the new formal support and the match to its intended use.

`run_review.py` copied the frozen source and author checks into this review's own `fresh/` directory, removed any previous local source olean, and ran the pinned Lean 4.34.1 compiler directly. The imported `KineticSupport.olean` was newly generated from that copy, with its own directory first on `LEAN_PATH`. The author olean was not used. All three positive runs passed without warnings:

1. Fresh compilation of all nine author theorems.
2. Author `Checks.lean`, with nine type displays and nine axiom reports.
3. Independent `TypedAudit.lean`, with nine explicitly written raw target statements, two exact evaluations of the simultaneous map, and three exact semantic counterchecks. All fourteen audit theorems compiled.

Every reported axiom list is exactly `[propext, Classical.choice, Quot.sound]`. There is no `sorryAx`, custom axiom, `sorry`, `admit`, `unsafe`, or `native_decide` in the author source. The raw wrappers ensure that an inadvertently weaker theorem type cannot pass just because its name still exists. They also confirm that the general replacement theorem needs only a normed additive commutative group, not an inner product.

The compiler is Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`, and the mathlib checkout revision is `d13f23b723b8a846827a245b89c10fc7d3f11612`. Existing compiled mathlib and dependency caches were reused read-only; rebuilding all dependencies or testing a fresh network installation was outside this audit. Direct compiler invocations requested writes only within this review directory. This is the usual Lean/mathlib trust base, not a claimed independent re-verification of the Lean kernel or all library oleans.

## Semantic findings

The elastic map is exactly the equal-mass rule in the pinned source:
`v' = v - <v-w,n> n`, `w' = w + <v-w,n> n`. Both formulas use the old `v,w`. Momentum conservation requires no unit assumption. Energy conservation explicitly requires `<n,n>=1`, the actual contact-normal condition. The algebra is valid for either normal orientation and does not need the incoming-flux condition; that extra physical admissibility condition belongs to the history construction.

The nested `Function.update` is a simultaneous update in the relevant sense: its right-hand expressions both evaluate `u i,u j`, never the partially updated function. The two labels are explicitly distinct in the total-energy theorem; all other labels are unchanged. The finite sum runs over the entire `Fintype`, so it is all-line energy, not only current physical lifetimes or one pair. The general replacement lemma's `hpair` premise is local pair conservation; this is neither an assumption of total conservation nor of the analytic theorem. The concrete collision theorem discharges that local premise using the proved collision-energy identity.

For any successful finite history, the use in Lemma W is ordinary induction over its finite event list: start from the independent birth-velocity vector, apply the concrete theorem at each C-event, and use the identity update at O-events. This yields the all-line sum equal to its initial sum. The induction and the construction of such successful all-time histories remain prose; the Lean package proves the needed single-event algebra only. It does not assert that the physical gas has already been constructed.

The four shift identities use affine origins and a fixed segment velocity. They have the correct minus sign for an origin shear and plus sign for shifting the event time. The repaired candidate's `A_p` is the affine origin of the **pre-first-event segment**. None of these declarations asserts the generally false identity `x_p(-theta)=A_p-theta*v_p` for an already scattered trajectory. Composing shears is proved for an affine origin; it is not a formalized group action on complete collision histories.

In particular `contact_time_shift` evaluates two shifted affine flights at the supplied time `t+theta`. It proves equality of their relative displacement with the original displacement at `t`. It has no entering-root definition, branch-choice condition, chronology predicate, or minimization over roots. It therefore supports a local contact equation once the root is translated; it does **not** prove that the actual determined entering root, its forward-ray lower bound, prefix success/abort, or the global chronology test covaries. Those remain the separate prose induction in Lemma W Claim 2. The README expressly makes this limitation, so there is no circular formal assumption pretending to establish the full covariance theorem.

The three rational calculations match the exact uses: the 22nd-moment Hölder exponent is `-1+(21/20)(21/22)=1/440`; with microscopic scale `alpha=mu^(-3/2)` and chaining parameter `theta=1/8`, `mu^(-1) alpha^(-4 theta)=mu^(-1/4)`; the remainder exponent is `1+4 theta=3/2<=2`. Lean proves rational arithmetic only. Substitution into real powers, asymptotic limits, Hölder, the maximal inequalities and probability bounds remain prose mathematics.

## Sensitivity and failure evidence

Four independently altered copies were rejected by Lean for mathematical proof failures, rather than missing imports or syntax errors:

| Mutation | Actual rejection |
|---|---|
| Change the plus in the right outgoing velocity to minus | Momentum and energy goals remain unsolved |
| Compute the right velocity from the newly computed left velocity | Concrete total-energy proof has a type mismatch against the pair-energy theorem |
| Replace `1/440` by `1/441` | The rational proof leaves `False` |
| Change one contact origin shear from minus to plus | The affine proof leaves an uncancelled `2*shift*v` term |

These failures are recorded in `logs/mutation-*.txt`. The original files were never altered. The three compiled exact counterchecks additionally show the semantic danger independently of whether an old proof script adapts: in the real line, `(v,w,n)=(1,0,2)` has outgoing squared energy 25 instead of 1; updating sequentially with `(1,0,1)` gives squared energy 0 instead of 1; and the wrong shear sign fails already at scalar origin 0, velocity 1, time 0 and shift 1. The nonunit and sequential counterchecks are proved by Lean over exact real numerals, not numerical sampling.

## Scope boundary and reproduction

The original analytic target remains the actual deterministic hard-sphere gas on full `R^3_x x R^3_v`, the entire supplied regular Boltzmann lifespan, unsmoothed fluctuations centered at the exact microscopic expectation, and convergence for every finite smooth compactly supported test vector in `J1` with C-tightness. None of the collision-history construction, physical-chart domination, covariance of the determined-root algorithm, measure-preserving change of variables, window estimate, Gaussian reserves, cumulant/increment estimates, microscopic union bound, C-tightness, or final path limit has been formalized here. The prior analytic PASS remains a prose proof verdict and is not promoted by this package into a Lean theorem.

Run `python run_review.py` from this directory (or by absolute path). It authenticates frozen inputs, recompiles its own copies, checks all axiom reports, and reruns the four expected-failure mutations. It uses the documented existing local Lean/mathlib cache. The machine-readable result is `validation.json`; detailed outputs are under `logs/`. This audit found no required repair within the advertised narrow scope.
