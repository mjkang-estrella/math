# H040 compressed information — raw Factory Opus report

Unaccepted proposer report. Mathematical assertions and provider usage footer require qualification; no usage figure is treated as research evidence.

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h040-compressed-information-factory-opus-20261008-r1`

Provider: acpRegistry_factory_droid / claude-opus-5-5; completed.

# H040 ideation: compressed public information and adaptive decoders

I'm submitting no cards. I looked at seven concrete operations. Each one either restates a mechanism the project already priced, or fails a gate I can state exactly on paper. Verified improvement is still **NONE**, and the best supported exponent is still 1/2.

**Scope of this pass.** I read RESEARCH_LOOP, RESEARCH_TEAM, all of STATE, and the accepted H036–H039 records. That includes H039 information, composition, arithmetic, hybrid-memory and grid-helper, plus the raw H039 hybrid prior-art report. I also read the information-lens records H002 G1/G2/L2, H003, H013 MCL and group-action features, H017, H018, H019, H020 shadow/structured, H021 and H026. I did no runs, imports, edits, children or commits. I read no H040 proposals and did not touch H006, H038 or the H039 hybrid.

**Primary sources.** I could not do fresh primary reads. FetchUrl only accepts URLs the user supplies, and WebSearch returned snippets only. So every literature fact below is either a project record of an earlier root read (marked "record") or my memory (marked "memory, unverified"). The derivations are my own paper algebra and have not been reviewed.

## One gate covers all the decoders on the table

All the decoders the project has considered estimate a phase. That includes active AGS/Kaliski queries (H003), MCL coset phase (H013), and the passive decoder in operation 1 below. If a feature has correlation ε = q^(−b) with a scalar character, the decoder needs about 1/ε² samples per phase it resolves.

The cleanest version is passive harvesting: N samples, each costing about one walk step, followed by a kangaroo search over the interval that remains. That costs about N + √(q/(ε√N)). The minimum is at N = (q/ε)^(2/5), which is below √q only when **b < 1/4**. With m = q^d this is the d → 0 limit of the H019 window b < 1/4 − d (record).

This gives two concrete cases:

- **Additive characters of k.** These are group characters, so the Kohel–Shparlinski bound applies (record: H002 G2, H026). It gives ε ≤ 2·d·L·√p/q, where d is the degree of a rational feature and L its additive-Fourier L1 norm. Passing the gate needs d·L ≳ q^(1/4). Reindexed features x∘[m] have large degree but no new signal: the transport identity only permutes frequencies.
- **Multiplicative characters of k.** The known ceiling is q^(−1/12)·log^(1/3) (record: Ahmadi–Shparlinski, H013). That is above the q^(−1/4) gate, so this window is genuinely open. But no candidate feature has been named for it, and I found none.

## Operations examined and not carded

1. **Passive bias harvesting during a kangaroo walk.**
   - Operation: start a walk from Q with jumps that are multiples of G only, so every point has the form Q + d_i·G with d_i known. Apply a public filter to each point and accumulate Σ f(P_i)·e(−a·d_i/q) to estimate e(ak/q). Finish with a kangaroo search over the remaining interval.
   - Changed paid operation: one filter evaluation and one complex accumulation per step. The bookkeeping is nearly free; feature evaluation is the real cost.
   - Gate: ε > q^(−1/4) (derived above). Bounded-degree x-features give ε ≈ q^(−1/2)·polylog, so they fail by a factor of q^(1/4).
   - Why not carded: it is a new decoder with no signal behind it. Low frequencies of the jump positions also alias, so the noise model is heuristic.
2. **The multiplicative version of operation 1.** Sample along ×2 or ×3 orbits c_(i+1) = 2c_i, so the character value updates by a fixed root of unity at O(1) cost. H013's progression sampler instead pays an F_q exponentiation per sample. That removes only polylog factors from the H013/H019 conditional cost m²/ρ² + √(q/m). It is a sampler improvement with no feature, and it is likely close to the H014 coset-backend recurrences.
3. **Branch transfer through a correspondence to an easy group.**
   - Operation: take x ↦ x + c onto the twist's ℓ-part, using Pohlig–Hellman, or onto power residues in F_p^*.
   - The sum over both branches is a homomorphism from a group of order q, so it vanishes (record: H039 coprime lemma). The power-residue case is already H027.
   - For a single branch, the fibre product C = E ×_(P¹) E^t has genus 1 + 1 + 2 = 4. A Weil-type bound for an unramified character gives |Σ| ≤ (2g−2)√p = 6√p, so ε = O(q^(−1/2)) (memory, unverified theorem).
   - Close to the twist notes in H019 and H036.
4. **Index recovery by bisection over interval products.**
   - Operation: test k ∈ [a, a+T) by evaluating ∏(X − x(jG)) at x(Q − aG) with the square-root Vélu index system, then halve the interval each round.
   - Cost: Σ Õ(√(q/2^i)) ≈ 2.41·√q·polylog, plus Õ(√q) memory.
   - This is valid and closes H002 G1's "membership does not return j" objection, but it loses to BSGS and rho by polylog factors. The project already records Vélu as one-point evaluation only (H020).
5. **A halving tree with interval certificates.** The correct branch at depth t has residual scalar in [0, q/2^t). Without a pruning signal, exploring the tree costs 2^t·√(q/2^t) = √(q·2^t) ≥ √q. This is the H039 halving operator relabelled as coset search.
6. **Features read on isogenous curves (Elkies isogenies).** Each pulled-back feature has bounded degree ℓ·d and obeys the transport identity (records: H018 N1, H026). No new signal.
7. **Out of scope or known.**
   - Twist and invalid-point ladders need an oracle that applies the secret scalar.
   - Lenstra's isomorphism E(F_p) ≅ End(E)/(π−1) is not effective (memory, unverified).
   - Using a coordinate set with cheaply decodable logs as the decoder is factor-base territory, which is the stopped H038 role, so I did not pursue it.

## What is missing

A usable signal needs one of these two things:

- **(M1)** A public feature F on E(F_p), computable in polylog time, with |E_n F([n]G)·χ̄(n)| ≥ q^(−b) for some multiplicative character χ of order m = q^d, where d > 0 and b < 1/4 − d.
- **(M2)** For additive characters, a feature whose effective degree times Fourier-L1 norm is at least q^(1/4), whose evaluation stays polylog, and which is not a reindexing x∘[m] or a bounded-degree correspondence.

None is known, and none of these operations supplies one. A cheap, decisive falsifier for any future named F is to compute exactly max over χ of |c_χ(F)| over the whole group on a few curves with q between about 2^12 and 2^14. That takes O(q log q) per curve via an FFT over F_q^*, compared against the random baseline of about √(log q / q). I'm proposing this only for when a candidate feature exists. Because the H034 cap is consumed, it would need a new admission before anyone runs it.

---
*Factory usage — local bridge. This turn: 2,835,808 tokens · ≈1,109,930 Factory credits. Saved session total: 2,835,808 tokens · ≈1,109,930 Factory credits (including recorded subagents). Credits are a local estimate, not a dollar charge.*
