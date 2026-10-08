# H031 portal/fold cost review: raw Factory Fable report

UNREVIEWED assertions preserved verbatim. See H031-autonomous-walk-screen.md
for accepted scope and root corrections; in particular segment laws, transferred
cycle frequencies, experimental power counts and external timing conversions
are not validated measurements of either proposed map.
Task: node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h031-portal-cost-fable-20261008-r1
Provider acpRegistry_factory_droid, model claude-fable-5.1; COMPLETED, no pending children.

# H031 Grok autonomous-walk cards: independent cost/protocol review

Read-only. No edits, runs, imports, children, staging or commits. Files read: RESEARCH_LOOP.md, RESEARCH_TEAM.md, research/STATE.md (first 879 lines, which cover the H031/H032 checkpoints), findings/H031-autonomous-grok-raw.md, H024-slope-active-kernel.md, H031-memory-disposition.md, plus root's existing H031-autonomous-walk-screen.md, H024-escape-finite-negative.md, H029-walk-stage0-review.md and the H025 bounded-stride passage. Cycle dynamics are left to the native math reviewer; where I touch them it is only because they fix the cost or stopping contract.

**Source access.** I fetched the primary BLS paper (cr.yp.to/elliptic/negation-20110102.pdf) with curl to /tmp and extracted text with pdftotext; the repository has no local copy. All BLS figures below are from that text. I did not read Wang–Zhang (cited by Grok) or re-read Kuhn–Struik/Bos–Kleinjung–Lenstra. No timings, GPU prices or hardware ratios are invented anywhere below.

## Verdict

**Recommendation: NO-RUN for both cards.** Neither falsifier as written could decide a complete-work improvement, and both cards fail paper gates that are already supported by existing evidence in this repository. Verified improvement remains NONE.

## 1. Strongest comparators

**Low memory (correct comparator for both cards): BLS 2011 negating r-adding walk, as measured, not as idealized.**
- Per iteration: 5M+1S, plus canonicalization (24.75 of 306.08 arithmetic instructions, about 0.57 M-equivalents on their platform), 6 subtractions, and (I−3M)/224 batching remainder (BLS §3 and "Overall performance", p.14).
- Measured 362 cycles per iteration against a 306.08 arithmetic lower bound; "under 4%" of cycles are attributable to negation handling (negating, 2-cycle detection every 48 iterations, doubling escape). The 18% gap is DP detection, loop control and call overhead.
- Measured iteration constants: 1.0789·√(πℓ/4) DPs at 50 bits (sd 0.558, CV ≈ 0.52) and 1.0074·√(πℓ/4) at 55 bits, both at DP rate 2^-20, r=2048.
- So the "0.886(5+s)√q" figure Grok uses is the (1+o(1)) heuristic for *BLS's own walk with r→∞*, not a measured constant, and not a law for either Grok map. At q≈2^16 it is also not what BLS would achieve: their own 50-bit measurement already sits 8% above it.

**High memory: H019 x-only BSGS**, leading coefficient (2√2/3)(2.5+s) ≈ 3.111 at s=0.8. Card 1's theoretical optimum (portals vanish, step count unchanged) is 0.886·(4+s) ≈ 4.254; Grok correctly concedes the cards do not reach this regime. I agree, and note that this means the cards can only ever be constant-factor claims against BLS.

## 2. Card 1: arithmetic gate, corrected

Grok writes the gate as ρ < s/(6+s). That is an algebra slip:

$$(4+s)+\rho(6+s) < 5+s \iff \rho < \frac{1}{6+s}.$$

At s=0.8 the threshold is 1/6.8 ≈ 0.147, not 0.118. Root's screen already states this; I confirm it independently. The consequence for the proposed falsifier: fixing ρ = s/(6+s) gives a subtotal 4+2s = 5.6 versus 5.8, so the experiment would only permit a step-count inflation of 29/28 ≈ 1.036 before all other costs. That is below the measurement noise of any single-seed test (see §5).

**Occupation-weighted frequency, not density.** ρ is the density of portal classes under the hash. The arithmetic depends on f = E[N_p]/E[W], the fraction of *executed* steps that are portals. The correct conditions are:

- Per-step leading: $(4+s) + f(6+s) < 5+s \iff f < 1/(6+s)$.
- With the two dependent inversion batches explicit, for a round of n walkers of which d portal:
  $$n(4+s) + d(6+s) + (1+\mathbf 1[d>0])(I/M-3) \;<\; n(5+s) + (I/M-3)$$
  i.e. $f < \big(1 - \mathbf 1[d>0](I/M-3)/n\big)/(6+s)$. The second batch is over only d ≈ fn elements, so its remainder amortizes worse than the first; negligible for large n, not for the small walker counts of a 2^16 test.
- Full matched condition (equal success law not assumed):
  $$E[W_{\rm card}]\big((4+s)+f(6+s)\big) + X_{\rm card} \;<\; E[W_{\rm BLS}](5+s) + X_{\rm BLS},$$
  where X collects hashing, canonical comparison, labels, DP handling, replay, restarts, cycle detection/escape, in-flight batch waste and setup.

**Segment form of the same gate.** Since the cheap step is ±G along a line of reflection classes, f = 1/(E[L]+1) where L is the number of fresh cheap steps per portal segment. Then

$$f < \frac{1}{6+s} \iff E[L] > 5+s = 5.8 \text{ at } s=0.8,$$

and this already *grants* free trap detection and an equal collision law. H024-escape-finite-negative measured 9 reversals in 13–18 attempted transitions on four fixtures (a reversal roughly every 1.4–2 steps), and the fixed-direction-per-class heuristic gives E[L] ≈ 2. So the existing finite evidence places E[L] at about a third of the required 5.8. The 10% gate in the H024 convention, (4+s)+f(6+s) ≤ 0.9(5+s), needs f ≤ (0.5−0.1s)/(6+s) ≈ 0.062, i.e. E[L] ≳ 15.

**Headroom ceiling.** Even at f→0 the arithmetic saving is bounded by (4+s)/(5+s) ≈ 17% of the 5M+S subtotal, which is the same order as the non-arithmetic overhead BLS measured (18% over their instruction lower bound) and far larger than their negation overhead (<4%). An arithmetic-subtotal comparison therefore cannot establish a full-cost gain; only a matched implementation could, and none is proposed or authorized.

**Inversions.** Grok does charge two dependent batches for the portal (10M+2S), consistent with H024's jump subtotal. The 4+s / 6+s split is correct. What is missing is that the escape step for any trapped stretch is *also* a two-batch jump and must be counted in f.

## 3. Card 2: arithmetic gate, corrected

Cost per accepted step is two full canonical additions, 2(5+s), with both denominators in one batch of 2n (Grok's 10M+2S is right). Condition against BLS:

$$E[W_{\rm card2}] < \tfrac12 E[W_{\rm BLS}] \iff \text{collision-rate enhancement } F > 4.$$

The only law on record is the iid minimum-of-m pushforward, F_m = m²/(2m−1), which gives F_2 = 4/3 and the ratio

$$\frac{m(5+s)}{\sqrt{F_m}\,(5+s)} = \sqrt{2m-1} \;\ge\; \sqrt 3 \approx 1.73 \quad (m\ge 2),$$

independent of s. So under the idealization no number of candidates pays, and m=2 loses by √3. This is a conditional idealization, not an EC theorem, exactly as H031-memory-disposition states for its Card 2. Grok's card is the same selection mechanism with a *worse* ledger: H031-memory Card 2 at 6M+2S already lost at (√3/2)(6+2s)/(5+s) ≥ 3√3/5 ≈ 1.039; Grok's 10M+2S loses at √3 for every s. It should be deduplicated against that screen rather than treated as a new candidate. Grok's own text concedes "a random function does not do that"; the card supplies no candidate-specific law, and image concentration sampling cannot supply one.

Two further cost consequences for the native reviewer's dynamics check: with two fixed jumps, BLS's own heuristic puts 2-cycle onset at ≈1/(2r) = 1/4 per step, and their optimal checking schedule loses about 1/√r ≈ 0.71 of an iteration per iteration at r=2. If that heuristic transfers, Card 2's per-step cost is closer to 2(5+s)·1.7 than to 2(5+s). I state this as BLS's formula applied to r=2, not as a measurement.

## 4. Missing contracts (both cards)

Root's screen lists several; I add the cost-relevant specifics.

**Card 1**
1. **Trap detection/escape.** The ±G step is deterministic per class, so a two-class fruitless cycle with no portal is permanent (root's closure argument). The card has no detection schedule, no escape operation and no cost for either. BLS's contract (check every w ≈ 2√r steps, store first s, escape by doubling) is the minimum template; the escape is a second two-batch jump and enters f.
2. **Null-hit policy is incoherent.** "Discard and keep walking" cannot work: the successor is a function of μ, so two colliding walkers have identical futures and every later meeting is also null; a single walker self-hitting a DP inside a cycle produces a null hit every two steps, each costing a replay of both trails (≈2/θ steps). The ledger line "null b-coefficient restarts" describes a different algorithm. A fixed rule is required: retire the walker, reseed with uniform fresh (a,b), charge all discarded steps and the replay.
3. **Portal label rule.** The (a,b)→(−a,−b) shortcut is specific to the +G step. After a jump the canonical flip gives (1−a−a_J, −b−b_J), not (−a−a_J, −b−b_J). "Apply the reflection rule" must be written out.
4. **Portal table and hash.** Size r_p of the jump set, the fixed public hash on the canonical μ representative, its per-step cost, and the DP predicate (also on μ) must be fixed before the walk is a defined function of class. r_p also governs portal→±G→portal short cycles.
5. **Exceptional dispatch** from H024: {O,G} sentinel, zero root, equal roots (G/2), P=±J at portals, zero denominators, each with its verification and restart cost.
6. **Memory ledger**: per walker (μ,u,a,b, seed, flags) versus BLS's 70 bytes/walk plus 102/16 for cycle watching; DP record format.
7. **Stopping**: first verified useful collision, fail-stop cap, in-flight batch waste, failed-trial accounting.

**Card 2**: label sign ε (root's point), tie dispatch on equal x, 2-cycle detection/escape at r=2 with its cost, null-hit/restart/stopping as above, and a competent control (large-r BLS with cycle check, not an r=2 walk).

## 5. Can the proposed experiments decide an improvement? No.

- **Comparator unmeasured.** Card 1's kill rule compares a measured candidate to the idealized 0.886(5+s)√q, which BLS themselves exceeded by 8% at 50 bits. Any decision needs a matched BLS control on the same curve, seeds, DP rule and cycle policy. Card 2 asks for such a control; Card 1 does not.
- **Margin versus variance.** The target effect at Grok's ρ is a 29/28 step factor. Rho collision times have CV ≈ 0.52 (BLS measured 0.558/1.0789). Resolving 3.6% at 2σ needs on the order of 800 independent completed solves per arm; one seed or one curve cannot do it. Even at the correct ρ the margin is zero.
- **Scale.** At q≈2^16 the idealized walk is ≈227 steps; DP waiting (n/θ) and portal/escape overheads are O(1)-per-walker effects that dominate at this size and do not scale like the claim. A single size cannot separate constant from scaling, and RESEARCH_LOOP requires increasing sizes and declared seeds.
- **Termination.** Without contracts 1–2 above, trapped walkers never terminate; the experiment cannot be run as specified, and adding the contracts silently would test a different algorithm (root's point).
- **Grok's secondary kill criterion** ("more than one step in six is a repeated class in a ±G stretch") is predicted on paper to fire: with trap pairs lacking a portal with probability (1−ρ)² ≈ 0.73–0.78 and E[L] ≈ 2, the repeated-class fraction is far above 1/6. A run would only confirm the already-recorded H024 finite evidence.

## 6. Tightly justified paper-first step (only if root wants to keep Card 1 alive)

A proponent must supply, on paper: (a) an explicit escape contract with per-step cost c_esc and (b) a derivation that under it the fresh-step segment mean satisfies E[L] > 5+s with the escape's two-batch cost included in f, and (c) an argument that line-structured fresh classes count as birthday samples (H025's bound 2(4sL+1)/q on cross-line signed collisions says adjacent classes on a line are not independent samples). If (b) cannot be met on paper, no synthetic run is informative. For Card 2 the only reopening evidence is a candidate-specific useful-collision law with F > 4; nothing weaker, and no image-size statistic, qualifies.

## 7. Retained possibilities (not excluded by this review)

- Portal constructions whose *cheap* step is not a ±G line (so stretches mix) and have f < 1/(6+s); none is on the table.
- Non-iid collision laws for selection walks (Card 2); unsupported, not disproved.
- Any claim about this map's actual stationary occupation; the fixed-direction coin model is a heuristic consistent with H024's finite data, not a theorem.

No universal statement about autonomous or coordinate walks follows; the cards fail their own gates under their own stated models plus existing finite evidence.
