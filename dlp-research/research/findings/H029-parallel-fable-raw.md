# H029 raw delegated report — not accepted wholesale

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h029-parallel-fullwork-fable-20261008-r1`
Provider/model: acpRegistry_factory_droid / claude-fable-5.1
Status: completed. Retrieved 2026-10-08. Root reconciliation pending; mathematical and source claims below are reviewer assertions.

# H029 initial ideation: parallel scheduling / memory organization / cross-batch work sharing

Read-only. No edits, experiments, imports, or children. Files read: `RESEARCH_LOOP.md`, `RESEARCH_TEAM.md`, `research/STATE.md` (latest checkpoints), `H013-scheduling-cards.md`, `H013-scheduling-preflight.md`, `H013-collision-baseline.md`, `H020-memory-cost-disposition.md`, `H020-memory-grok-raw.md`, `H025-signed-layouts.md`, `H028-unit-event-kernel-negative.md`, `H015-winnowing-screen.md`, `H002-sol-tradeoff-cards.md`. No other H029 proposal read. External sources (BLS 2011, van Oorschot–Wiener, GWZ 2017) were **not** reopened this session; I use only what the repository already records from them plus memory, labelled below.

## Bottom line first

**No mechanism in this lens survives its own paper falsifier.** I supply three distinct concrete mechanisms (not renamed batch inversion/DP/parallel rho), each with an exact falsifier that I carried out, plus the ledger that explains why the lens has no 10% complete-work headroom at realistic parallelism-to-memory ratios. This is an honest scoped negative, not padding; the single inequality that would reopen the lens is stated at the end.

## Matched competent baseline B0 (what every card must beat)

BLS-style parallel negation rho (as recorded in `H013-collision-baseline.md`): P live walks on m nodes, w = P/m walks per inversion batch, r-adding walk with jumps J_s = u_sG + v_sQ, canonical sign, coefficient-free walkers with seed replay, DP predicate on canonical x-hash with density θ, DP store of M = θ·T records (hash, seed, length), cycle checks with doubling escape, abort beyond ~20/θ.

Per step: (5 − 3/w)M + 1S + I/w. Total steps:

$$T_{\text{tot}} \approx \sqrt{\pi q/4}\,(1 + c_r) + c_{\text{tail}}\,P/\theta,\qquad M = \theta\sqrt{\pi q/4}$$

Removable overhead pool, with everything else being the irreducible birthday term:

| Term | Source | P=2^30, M=2^35, w=2^10, I=8M, s=0.8 | P=2^30, M=2^40 |
|---|---|---|---|
| Tail waste c_tail·P/M | vOW heuristic c_tail≈2.5 (memory, unverified); floor is 1 | 7.8% | 0.24% |
| Cycle/non-randomness c_r | BLS heuristic 1+Θ(1/√r), r=2048 (recorded in W019 audit) | ~2% × unknown constant | same |
| Inversion (I−3M)/(w(5M+S)) | BLS batch ledger | 0.08% | 0.08% |
| Initial scalar mults P·1.5·log₂q / T | setup | ≈ 2^-89 | ≈ 2^-89 |

Two consequences frame all cards:

1. Scheduling, communication, and memory organization can only touch this pool. It exceeds 10% only when **P/M ≳ 0.03**, i.e. a campaign that is memory-starved relative to its live-walk count. The known remedy there (fewer live walks per unit DP memory, costing wall time only) already exists in vOW/BLS and is not a discovery.
2. The high-memory x-only block BSGS regime (≈0.62× rho field work per `H020-memory-grok-raw.md`, qualified in `H020-memory-cost-disposition.md`) needs M ≳ 0.19√q group elements. For a 256-bit target that is ~2^125 records. So for full-size targets the parallel question is the rho ledger alone; distributed-table organization for BSGS is a feasibility question, not a work question.

## Lemma used by all three cards (coalescence lock)

For DP detection to work, the successor of a point must be a function of that point alone. Hence each walked step must compute its own slope with its own denominator x_X − x_{J_{s(X)}}. The only arithmetic shareable across walkers is the inversion (already batched). Any cheaper "second point" from a shared denominator is either not walked (H018/H019 side images, noncoalescent, already rejected) or becomes a new walker (Card A).

---

## Card A: coalescent twin branching at retirement

**Public state/update.** B0 plus a per-node branch budget. At a branch event, walker at X with jump s computes both X + J_s (its own successor) and X − J_s from the shared denominator: extra cost 2M + 1S for a second walked point, versus 5M + 1S for an ordinary step. The twin becomes a new live walker with virtual labels (a − u_s, b − v_s); the branch is recorded as (parent seed, step index, sign) so replay reconstructs labels along a branch chain. To hold P fixed, one walker is retired per branch.

**Recovery.** Unchanged: on a DP match, replay both segments through their branch chains, k = (a₁−a₂)/(b₂−b₁) mod q, verify kG = Q.

**Hoped benefit.** ~3M saved per branched point, so a fraction ρ of branched steps saves ≈ 0.52ρ of field work (s = 0.8).

**Costs.** Branch records, longer replay chains, and the critical one: a walker retired at a non-DP point leaves a *dark tail* (its points since its last DP). A later walker merging into the dark tail recomputes the path to the retirement point and beyond, and stores a fresh DP; the collision goes undetected. Dark points therefore lose their value as birthday targets.

**Unsupported assumption.** That retirements can be timed so dark tails are negligible while the branch rate stays material.

**Prior art distinction.** Not H018 side images (those are not walked). Not tag tracing / Cheon–Hong–Kim macro words (H020 Card 1). Not Teske mixed walks.

**Decisive paper falsifier (carried out).** Let ρ be the branch rate per walker-step.
- Retire at arbitrary points: dark fraction ≈ ρ/θ, birthday penalty ≈ ρ/(2θ) relative work. Net gain iff 0.52ρ > ρ/(2θ), i.e. θ > (5M+S)/(6M) ≈ 0.97: essentially every point stored. That is the Θ(T) memory regime where block BSGS already wins outright.
- Retire only at DP arrivals (zero dark tail): ρ ≤ θ, gain ≤ 0.52θ. At θ = 2^-20 the gain is below 10^-6.
- Let P grow instead of retiring: gain ≤ 0.52·P_final/T, and live state P_final·2log₂q bits ≤ memory gives gain ≤ 0.26θ.

**Verdict:** killed on paper in every low-memory regime. Worth retaining as the scoped reason denominator sharing cannot enter a coalescent walk.

---

## Card B: adaptive DP density under fixed memory

**Public state/update.** B0 with a time- or walker-dependent storage rate θ_i (threshold h(t) on the canonical x-hash, or walker classes with different thresholds). Lookup at every point satisfying the loosest threshold still in effect.

**Hoped benefit.** Cut the tail-waste term c_tail·P/θ by storing more densely where collisions are more likely to land, at the same M.

**Costs.** Threshold bookkeeping; for nested thresholds, lookups must use the loosest threshold or detection of older, denser-stored points is lost; pure position-based storage (every L steps) is not a point predicate and forces a lookup every step.

**Unsupported assumption.** That merge positions are non-uniform over visited points. They are uniform: every visited point is equally likely to be the merge target.

**Prior art distinction.** H015 covers the *report rule* (winnowing); this card is about the *rate schedule*. vOW/BLS use constant θ.

**Decisive paper falsifier (carried out).** With Bernoulli storage at rate θ_i on visited point i, M = Σθ_i, and uniform merge position, mean delay ≈ (1/T)·Σ 1/θ_i ≥ T/M by AM–HM, with equality iff θ_i is constant. So no Bernoulli density schedule lowers mean delay at equal memory. Deterministic equal spacing would halve the mean gap (T/(2M)) but requires per-step lookups: one lookup per step in the equal-cost cell ledger adds ~1/5.8 ≈ 17% to every step, far exceeding the ≤ 2.5P/M it could remove. H015 already shows the point-based bounded-gap substitute has *worse* mean delay (0.61w vs 0.5w).

**Verdict:** killed. Caveat retained: schedules can change delay *variance* or worst case (useful for abort policy), not expected work.

---

## Card C: full-trail walkers for a memory fraction

**Public state/update.** Allocate M₁ of the DP memory to storing *every* point of a subset of walkers' trails (φ = M₁/T of all visited points), the remaining M₂ = M − M₁ to ordinary DPs. A merge into a fully stored trail is detected immediately (zero tail waste); other merges pay the DP delay 1/θ₂ = T/M₂.

**Hoped benefit.** Remove tail waste for a fraction φ of collisions.

**Costs.** Per-step insert for full-trail walkers; full-trail records carry a point, not just a hash.

**Unsupported assumption.** That immediate detection on a fraction of trails outweighs the thinner DP density on the rest.

**Decisive paper falsifier (carried out).** Mixed waste ∝ (1−φ)·P·T/(M−φT) versus DP-only ∝ P·T/M. Mixed is worse iff (1−φ)M ≥ M − φT iff T ≥ M, which holds in every regime where rho is used at all.

**Verdict:** killed.

---

## Ideas considered and dropped without a card (one line each, to avoid re-proposal)

- Walker-population taper near expected end: equivalent to choosing smaller P; vOW tradeoff, wall time only.
- Local per-node fine-DP tables: catch only the w/P fraction of merges within a node.
- Gossip of fine DPs: equals raising global θ, i.e. more memory.
- Pair-coupled successors (X_A ± X_B sharing a denominator): position-dependent, noncoalescent, detection thinned by θ.
- Two walk functions / epoch-rotated jump tables: cross-class merges stop coalescing; strictly worse.
- Rho walkers probing a baby table of b ≤ M entries: saves ≈ b steps of √q; nil at any realistic M.
- Cheaper restarts (DP + G), chained replay: restarts are rare in B0; nil.
- H013 A/B/C memory-traffic cards: already preflighted negative; not repeated.

## Wave items

1. **Best supported work:** B0 ledger above; generic exponent 1/2 with known constants, all setup/memory/tails charged.
2. **Verified improvement:** NONE.
3. **Hypothesis under this lens:** that parallel scheduling, communication, or cross-batch sharing can remove ≥ 10% of complete work. Three concrete mechanisms were specified.
4. **Evidence:** all three fail their paper falsifiers (Card A: dark-tail/retirement coupling, gain ≤ 0.52θ; Card B: AM–HM optimality of constant θ; Card C: T ≥ M inequality). The total removable pool is c_r + 2.5P/M + (I−3M)/(w(5M+S)), below 10% unless P/M ≳ 0.03.
5. **Reopen condition (the only decisive test left in this lens):** a named campaign configuration under the project's event ledger where **c_tail·P/M + c_r ≥ 0.10**. If no such configuration is credible, park the lens; if one is, the competent remedy is already the known P-versus-M tradeoff, and the research question becomes measuring c_tail and c_r exactly, not a new mechanism.

**Prior-art status, honestly:** BLS 2011 and GWZ 2017 content comes from the repository's recorded primary reads; the vOW 2.5/θ constant is from memory and is also echoed in `H020-memory-cost-fable-raw.md` (as n/θ). None reopened this session; treat those constants as unverified here. No GPU/AI-FLOPS rate, precomputation, or multi-target amortization is used anywhere above.
