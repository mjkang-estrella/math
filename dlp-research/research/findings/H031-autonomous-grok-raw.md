# H031 autonomous-walk Grok raw report

UNREVIEWED claims retained verbatim; proposed experiments are not authorized.
Task: node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h031-autonomous-walks-grok-20261008-r1
Provider grok, model grok-4.7; COMPLETED, no pending children. No reported edits/runs.

No experiment was run and no file was changed. Verified improvement remains NONE. Two mechanisms survive this lens; a third would only retune a parked clock, a bounded-stride walk, or a formula whose multiplication count already loses.

Comparators used below: negation-aware Pollard rho as in Bernstein–Lange–Schwabe 2011, §§2–3 (one batched addition = 5M+S on the negation quotient, heuristic length (1+o(1))√(πq/4)), and the high-memory x-only block BSGS screen at limiting 2.5M+S per emitted key. Cycle escape, labels, hashes, replay, and in-flight batches are outside the 5M+S subtotal and are charged in the contracts. Pages 11–26 of the BLS paper were not read.

## Card 1 — Hash-timed portal on the reflection quotient

**Operation.** Work on the reflection class of P, published as the one-field key μ from the slope kernel. Both shifted abscissae are the two roots of the quadratic in μ, and the active root u is the canonical minimum, so the successor is a function of μ alone. State space (q+1)/2. Labels stay the affine pair (a, b).

- With probability 1−ρ, ρ a fixed public constant, take the ordinary slope step of +G: μ′ = −μ + 2h/u, then the new canonical root. Batched cost 4M+S, one inversion. If z ≤ u, labels go (a, b) → (a+1, b); if z > u, the output is the reflected point and labels go to (−a, −b).
- With probability ρ, and only when a fixed hash of μ says so (the hash is read before any arithmetic, not when a reversal is noticed), replace that step by one unbounded table jump J_ψ(μ). Use the already counted two-batch jump: recover y, add J, rebuild μ. Leading cost 10M+2S, two dependent inversion batches, both charged even if the batch is shared. Labels add the public coefficients of J, then apply the reflection rule if the rebuilt representative flips.
- Distinguished points are a predicate of μ only. A stored hit replays both seeds. Accept the collision only when the coefficient of k is nonzero; otherwise discard and keep walking, and charge the replay.
- Parallel copies share the inversion batches. On a confirmed useful hit, stop the batch and charge every in-flight denominator already formed. No per-walker ring, no second free inversion, no lookahead past the hash.

This is not a global clock and not “double when z > u”. The portal time depends only on μ.

**Gain.** Same quotient size as negation rho. Cheap steps are 4M+S against 5M+S. Average arithmetic (4+s) + ρ(6+s) beats 5+s only if ρ < s/(6+s). At the hypothetical ratio s = S/M = 0.8 that is ρ < 0.118. The exponent stays 1/2. The constant improves only if those rarer portals keep the number of μ-steps inside a factor (5+s)/((4+s)+ρ(6+s)) of the BLS length.

**Baseline.** Low memory: BLS. High memory: this card does not compete with x-only BSGS; memory is the DP table plus O(1) fields per walker.

**Costs.** One extra inversion batch on the portal fraction ρ. Hash, root comparison, label update, null b-coefficient restarts, and the aborted batch are paid. A portal that lands on O, G, or a zero denominator restarts that walker and throws away its steps. Precomputation is the jump table and the constants of G, once.

**Prior art.** The slope step and the two-batch jump cost are the H024 kernel, not a new formula. BLS and Wang–Zhang 2011/008 already double to leave fruitless cycles; the portal here is a class-hash jump, not that escape. H025’s O(sL) bound does not apply to the portal steps because those jumps are unbounded. It still applies to any stretch that only does ±G.

**Assumption.** Unproved: with ρ at the gate above, wasted 2-cycles on the ±G stretches multiply the step count by less than the arithmetic saving. No random-map constant is claimed for this graph. If the ±G stretches behave like the known length-≤2 cycles, the assumption is false.

**Falsifier.** One ordinary prime-order curve, q ≈ 2^16, full-length scalar, not the forbidden three-torsion start. Fix ρ = s/(6+s) at s = 0.8. Run the exact map, charge both inversion batches, restarts, and aborted batches, and stop at the first useful label collision. Kill the card if the mean field-work proxy is at least the BLS proxy 0.886(5+s)√q, or if more than about one step in six is a repeated class inside a ±G stretch.

## Card 2 — One-step fold of two translates

**Operation.** State is the BLS even-y representative W, labels (a, b). The published key is x(W). Two fixed jumps J and K have public coefficients and nonzero coefficients of k.

Each step, form both denominators x(W)−x(J) and x(W)−x(K) from the current point, before any inverse. Invert them in the same Montgomery batch as the other walkers. Compute both canonical images |W+J| and |W+K| at a full batched addition each (5M+S each; sharing the batch does not make the second addition free). Keep the image whose canonical x is smaller, and add that jump’s coefficients to (a, b). The other image is discarded and is not stored.

The successor is a function of W alone, so distinguished points on x coalesce. Replay from the seed on a DP hit. Reject a zero coefficient of k and charge the replay. Parallel walkers stop on the first useful hit and pay the open batch. No ring and no second sequential inverse.

**Gain.** The fold costs about two additions per accepted step, so the field proxy is about 2(5+s) per step. It beats BLS only if the mean number of steps to a useful collision is less than half the BLS length. A factor of two is the whole budget: hashes and discards sit on top. This is a constant-factor bet, not an exponent bet. It does not beat x-only BSGS unless the same cut also beats a method that already emits keys at 2.5M+S.

**Baseline.** BLS at one addition per step on the same quotient. High-memory comparator as above, which this memory regime does not reach.

**Costs.** The discarded branch is paid in full. Exceptions (equal x, infinity, zero denominator) restart the walker. DP storage, seed replay, and the in-flight batch are paid. Precomputation is two jumps.

**Prior art.** This is not the H018/H019 side-image x(P−J), which stays on one jump and was a predecessor identity. It is not an H029 twin branch: population stays one walker, and the unused point is dropped rather than retired into a trail. Negation canonicalization and the batch are BLS’s.

**Assumption.** Unproved, and strong: folding two translates by minimum x cuts the mean useful collision length by more than two on the negation quotient. A random function does not do that. Nothing here proves this fold does.

**Falsifier.** Same curve class as Card 1, q ≈ 2^16. Compare mean accepted steps of this exact map with mean steps of BLS on the same curve, same DP rule, and the same number of random seeds. Kill it if the step ratio is greater than 1/2 after both additions, discards, and restarts are counted. Image-size sampling is not enough; the kill is on useful labelled collisions.

## Not carded

Sticky differential shortcuts on the negation quotient lose once even-y is rebuilt (the known 3M recovery exceeds the saved squaring). Oriented x-only steps at 5M lose the √2 quotient factor under a random-map comparison, and that comparison is not being replaced by a proved shorter law. Same-time flocks and short lag buffers do not change the leading term once staggered hits and in-flight work are priced. Translate probes stored only at distinguished points contribute on the order of θ² expected hits in a low-memory run, which is not a second birthday channel.
