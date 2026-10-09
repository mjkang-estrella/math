# H042 orbit construction round2 — raw Claude report

Unaccepted construction report; success-probability and solver-cost claims require correction.
Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h042-orbit-construction-opus-20261009-r2`
Provider: claudeAgent / claude-opus-5-5. Completed; no claimed complete-work gain.

**I found no useful construction.** What follows is the strongest concrete schedule I can write for the orbit variant and why it stops short. I made no runs, edits, imports, child agents or commits, and opened no web sources. H006, H038, H039, H034 and the other H042 proposal were not touched.

## 1. Pattern solving with a structured seed set gains nothing

Take a PKM-type chain-structured seed set S0, with |S0| = B0, and layers [ℓ^(−i)]S0.

- **Per-pattern yield equals a fresh seed-only attempt.** Fix one exponent pattern c = (c_1..c_m). Its system asks for P_j ∈ S0 with Σ[ℓ^(−c_j)]P_j = R. The map P ↦ [ℓ^(−c)]P is a bijection, so the expected number of hits is about B0^m/q. Each hit is one row over the same B0 seed columns. A fresh random R decomposed over S0 alone gives the same expected yield. This is heuristic, at the same level as σ itself.
- **So per-pattern solving reduces to seed-only PKM at size B0.** Only the per-variable maps differ. Shrinking B is already inside the baseline's own optimisation, so this adds nothing.
- **Shared work across patterns forces an unstructured system.** Sharing work across the t^m patterns means solving over the union. In x-variables, each layer's root set is the rational part of L0∘φ_{ℓ^c}. Those layer polynomials are unstructured, and their product is a plain degree-B polynomial L_V. The only alternative is y-variables with the inflated composed equations. So keeping the chain structure and sharing pattern work are mutually exclusive in either representation.

## 2. The concrete construction: drop structure, use the plain union system

This is the one schedule that genuinely beats its matched baseline.

**Representation.**
- V = {[ℓ^i]G : i < B}, with ℓ = 2 so each step is one doubling. That is t = B layers over the single seed G, so B0 = 1 and every log is known.
- Membership polynomial: L_V(x) = ∏_{v∈V}(x − x(v)), degree B.
- Per-attempt system: ⟨S_{m+1}(x_1..x_m, x(R)), L_V(x_j)⟩, with R = aG + bQ and b ≠ 0.
- This is exactly PKM's plain-Semaev system at the same degree B, so D and σ are the same as the matched baseline. That assumes the solver is blind to which degree-B polynomial L is.

**Setup (A = Õ(B)).**
- B doublings to build V.
- A product tree to form L_V.
- A hash table x ↦ i with B records.
- A distinctness check: require ord(ℓ mod q) > 2B, or detect a collision in the table. This rules out [ℓ^i]G = ±[ℓ^j]G.

**Extraction and witness.**
- For each F_p solution, lift each x_j with one square root.
- Test at most 2^(m−1) sign vectors ε by group addition until Σε_j P_j = ±R.
- Look up each i_j in the hash table.
- Coefficients are ε_j·ℓ^(i_j) mod q. A repeated point, or a repeated layer, just adds coefficients. Cancellation would need ℓ^(i−i′) ≡ ∓1, which the order condition excludes.
- Spurious solutions cannot occur, because every root of L_V is rational. Failed attempts are still charged.

**Recovery.** One relation suffices, with no linear algebra: log Q = (Σε_jℓ^(i_j) − a)/b, then verify with one scalar multiplication. Rank is trivially 1.

**Invoice.**
- Orbit collapse: Õ(B) + D_plain(B)/σ.
- Matched baseline: Õ(B) + B·D_plain(B)/σ + L(B).
- In exponents, the gate moves from 1/m + d + s < 1/2 to d + s < 1/2.
- Intermediate t (B0 = B/t unknown seeds) gives max(1/m − τ + d + s, 2(1/m − τ), 1/m) with t = p^τ. This is minimised at τ = 1/m, so full collapse dominates every intermediate t.

**Why this is not a gain.**
- At full collapse the multiplier ℓ plays no role. Any known-log set, such as {[i]G}, behaves the same.
- The whole variant therefore reduces to a single point-decomposition instance with known logs: an m-term sum problem over the group, encoded through x-coordinates.
- Every explicit structure-blind schedule I can write lands at Õ(√p) or worse:
  - **m = 2:** form ∏_v S_3(x_1, v, X) by product tree, then take its gcd with L_V. That is Õ(B) per attempt, σ is constant at B ≈ √p, so the total is Õ(√p). This is BSGS in disguise.
  - **m ≥ 3:** enumerate m−2 factor-base elements and run the m=2 routine on the rest, so D ≈ B^(m−1). Then D/σ ≈ p/B, which balances against setup B at Õ(√p). Elimination through split auxiliary variables, u ∈ x(V+V), pays degree about B^(m−1) as well. That is a cost of these schedules, not a lower bound.
- Beating 1/2 would need a plain-L, structure-blind solver with D(B)·p/B^m below √p. That is precisely the "unknown solver" the brief excludes. The variant contributes the gate relaxation by 1/m and nothing more.

## Disposition

- The orbit card closes as follows:
  - **Structured S0:** no gain without shared pattern work.
  - **Shared pattern work:** forces the plain union system.
  - **Plain union system:** the variant's maximum effect is to delete the relation-count and linear-algebra terms. The remaining cost is one known-log decomposition, whose known schedules are all at least √p.
- No cheap falsifier separates total work any further, because the invoice is now an identity in D_plain. No experiment is justified.
- I made no novelty claim for the known-log collapse, which is probably folklore, and did not check prior art.
- Verified complete-work improvement: NONE. The best supported exponent stays at 1/2.
