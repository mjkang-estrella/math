# H035 Opus round 2 — retained reviewer report

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h035-hash-fusion-priorart-opus-20261008-r2`

Status: completed; no pending children. This is reviewer testimony; root qualifications and accepted scope are separate. Numerical hardware estimates here are not calibrated measurements.

I've finished reading the sources. Writing up the round-2 report now.

# H035 round-2 review (read-only)

## Bottom line

- **Within the H034 contract, the fusion saving survives against a properly matched word hash.** For p ≡ 3 mod 4 and in operation counts, it saves 2d–3d word multiplies plus about 3d–5d word adds per queried key, against the cheapest proven strongly-universal word hash I identified (C1 below). I said in round 1 that it saves M+A. That figure is only right against the field-affine comparator, which is not competent.
- **It does not defeat that comparator everywhere.** When p ≡ 1 mod 4, a square-only key only has a 2/H bound, and an exact-uniform key costs a ν-multiply on half of runs. In that case C1 may tie or win, and this is unresolved.
- **It is common-mode, so it gives H034 no advantage over H019.** Full-size improvement: still NONE.

## 1. My round-1 claims that I withdraw

- I said "−K has multiplier −η, still uniform, protocol-identical." **This is false.** The sign is chosen by the class of η, so both classes end up as square multipliers. I accept the root/Astra correction.
- I said "saving zero against standard bits" and "weakly beats every word hash." Both are withdrawn as stated.
  - Raw bits (C0) cost nothing but do not give the matched guarantee (see §3).
  - Dominance holds only against the specific comparators priced below. It is in op counts only, and only for H034's structure (no stored-point updates).
- I said "Thorup §3.5: pair-multiply-shift halves the multiplies." In v9, strong universality of pair-multiply-shift is left as **Exercise 3.10**, not proved. My comparator therefore relies only on Theorem 3.7.
- I said the change "tightens the H034 gate." Corrected version: under fixed Δ, z, h it weakly lowers the candidate's relative margin, and only through the aΔ + fzh terms (§5).

## 2. Strongest correct scope after the corrections

**Mechanism.** The square-only shifted model is X = u²x + r, Y = u³y. A leaf key is L = (uλ)² − (Xᵢ + Xⱼ) = u²·x(Pᵢ±Pⱼ) − 2r. It is computed from the canonical representative, then bucketed by (L mod p) mod H.

**Two H034-specific simplifications I derived (please check):**
- **Seeds never meet leaves.** The contract says seed keys are never compared with leaf keys, so the seed index can use X itself, which is also square-affine. It does not need X − 3r. H034 roots are static and the leaf phase has no doubling, so the "+3r on update" and new-cubic-doubling charges do not occur in H034.
  - In H034 the fused scheme's only extra costs are setup: one random u, one random r, and u² and u³ (1S + 1M).
  - The per-root transform costs about 1M + 1A if the multiply by u is folded into the batch affine conversion (uZ⁻¹), or 2M + 1A if done naively. There are 2ℓ² roots (ℓ here is the graph prime), so this is lower order.
  - **Per-key extra cost over the raw 6A kernel is exactly zero.**
  - H019 does pay the center charges (Xout = L + 3r, role-consistent shifts).
- **Montgomery form does not change the multiplier class.** R = 2^{64d} is an even power of 2, so it is always a square. The multiplier u²R stays square-only. Other representations, such as BLS's 76439-scaled form, would need their class checked.

**Collision law, now in closed form.** With buckets as residues mod H of [0, p) and K = ⌊(p−1)/H⌋:

    C0 = 2·Σ_{k=1..K} (p − kH)
    Z  = χ(H)·(1 + χ(−1))·Σ_{k=1..K} (p − kH)·χ(k)

- **p ≡ 3 mod 4:** Z = 0 identically. This confirms Astra's reversal result directly: pair collision equals the full-affine value C0/(p(p−1)), which is below 1/H.
- **p ≡ 1 mod 4:** the worst-case factor is 1 + |S|/Σ(p − kH), where S = Σ(p−kH)χ(k) is a weighted character sum of length about p/H, which is about √p in H034.
- **Check:** for p = 5, H = 2, the formula gives C0 = 8, Z = −4, and probability 3/5 at δ = 2. This matches Astra's counterexample.
- **Burgess sketch (unverified constants, not relied on):** it suggests the factor is 1 + O(p^{−1/16} log p). Pólya–Vinogradov alone is trivial at length √p.

**What the scope is, stated as narrowly as the evidence allows:** a shared, attack-agnostic way to obtain a pairwise-universal bucket hash of exact x at zero per-key arithmetic, for p ≡ 3 mod 4. Its magnitude is capped by the cost of the cheapest matched word hash. It is not a lookup-memory saving, not specific to H034, and no novelty is claimed.

## 3. Matched comparator

**C1: vector multiply-shift on the canonical key (Thorup v9, Thm 3.7, eq. 17; read).**

| Item | Specification |
|---|---|
| Key | canonical x ∈ [0, p), in any fixed bijective encoding. The Montgomery-canonical xR mod p works, so no conversion out of Montgomery form is needed. Canonicalization is required for every arm anyway. |
| Words | d = ⌈log₂p / 64⌉ input words, w = 64 |
| Intermediate width | w̄ ≥ w + ℓ − 1, where ℓ = log₂H. So w̄ = 128 for ℓ ≤ 65, and w̄ = 192 for 66 ≤ ℓ ≤ 129. |
| Seeds | a₀…a_{d−1} and b, uniform in [2^w̄] (not restricted to odd values) |
| Setup / storage | (d+1)·w̄ random bits. For p < 2²⁵⁶: 80 B at w̄ = 128, or 120 B at w̄ = 192. Seeds stay in L1. |
| Hash | (Σ aᵢxᵢ + b) mod 2^w̄, then take bits [w̄ − ℓ, w̄). For power-of-two H this is a shift; no mod-H work. |
| Per-key cost | 2d word multiplies (one 64×64→128 plus one low 64-bit) and about 3d + 3 adds/shifts when w̄ = 128. 3d multiplies when w̄ = 192. For d = 4 that is 8 or 12 multiplies. |
| Guarantee | Strongly universal, so pair collision is exactly 2^{−ℓ} = 1/H. This matches the 1/H + 1/(p−1) that H034's bound needs, which only uses pairwise collisions. |

**C1's cost in field-M terms.** These are my standard multiply-count estimates, not read from a source in this round:
- Generic d-limb Montgomery M (CIOS) takes about 2d² + d multiplies. That puts C1 at about 0.22–0.33 M for d = 4, and about 0.4–0.6 M for d = 2.
- With pseudo-Mersenne arithmetic, M is cheaper, so C1 is about 0.4–1 M.
- These are counts, not timings. Multiplier-port and dependency behaviour are platform questions.

**Alternatives I rejected as weaker:**
- **Plain multiply-shift (Thorup §2.3):** only 2/H. That doubles a leading false-probe term.
- **Simple tabulation (Pătraşcu–Thorup, read):** 3-independent with totally random tables. On a 256-bit key it needs either 32 lookups with 64 KiB of tables, or 16 lookups with 8 MiB. Also, a PRNG fill does not instantiate the theorem.
- **C0, raw canonical bits:** not matched. H034 leaf points are pairwise uniform in the group, but bounding the bucket population of x mod H at H ≈ √p hits the same √p-length character-sum barrier: the per-class Weil-plus-completion error is about as large as the main term. It is also coupled to the stopping time, which is exactly the decoupling the independent hash was introduced to avoid. I did not attempt an averaged argument.

**Verdict by case:**
- **p ≡ 3 mod 4, H034:** fusion strictly preserves the saving c_C1 per queried key (overshoot keys included) at matched-or-better pair collision.
  - As a fraction of arithmetic alone, it is at most about c_C1 / (2.5M + S + 3A). That is roughly 7% in generic 256-bit multiply-count terms, and smaller once the random-access head/node traffic in L is added.
- **p ≡ 1 mod 4:** either accept the 2/H bound (worse than C1) or pay for the exact-uniform ν-multiply. e is a per-run bit, so there is no per-key branch, and a small ν costs much less than a general M. Fusion vs C1 is undecided here, and C1 can win.
- **H019:** the per-center +3r, transformed doubling, and walk-selector issues come back into play. They are lower order only under its growing-block schedule.

## 4. BLS (local author PDF dated 2011-01-02, read from /tmp/h035lit.gQNd)

- The prime is p = (2¹²⁸ − 3)/76439, not 2¹²⁸ − 3.
- They compute s = 76439·y mod (2¹²⁸ − 3). That is "a unique representative of y mod p, represented as 76439(y mod p)". The fixed cofactor exists to make canonicalization cheap. It is not a mixing multiplier. They mention Montgomery y·2⁻¹⁶ as the alternative.
- The table index is s₀ mod 2048 for the **r-adding-walk precomputed table**, not an archive hash. Canonical y also decides negation and defines distinguished points.
- They explicitly do not claim that (s₀…s₉) is always uniquely determined, only that non-uniqueness is improbable. **That is not acceptable for H034's exact-equality semantics.**
- **Relevance:** this is prior art for taking an index from a fixed scaled canonical representative, with the scaling folded into normalization that is needed anyway. It is not prior art for a seeded scale used as a universal hash, and it provides no collision guarantee.
- **Rates do not transfer.** The 24.75 instructions for canonicalization out of 306.08 total are Cell SPE figures in radix 2^12.8.

## 5. Cheapest next decisive analytical gate (paper only, no benchmark)

**G1: materiality to H034.** In the gate [(1−f)b−a]·gB > aΔ + fzh, substitute gB ← gB − (M+A) + c_X for c_X ∈ {0 (F), c_C1}, applied to both arms.
- The relative margin is ([(1−f)b−a]·gB − aΔ − fzh)/(b·gB). Its derivative with respect to gB is proportional to aΔ + fzh.
- So a cheaper common hash changes nothing if Δ = z = 0, and only weakly hurts the candidate if Δ ≥ 0.
- The one open sub-step is to confirm that the hash price enters Δ = LC − LB symmetrically. Hash masking is listed inside L on both arms.
- If confirmed, H035 has no bearing on the H034-vs-H019 ranking, and it should be archived as a shared implementation note.

**G2: only if universal claims are wanted.** Either restrict all square-only claims to p ≡ 3 mod 4, which needs no work, or bound ρ(p, H) = |S|/Σ(p − kH) explicitly for the H ≈ √p regime.
- For concrete small instances, ρ is an exact O(√p) evaluation of the formula. That is a certificate, not a benchmark.

Beyond G1 and G2, the gap between F and C1 is a hardware price ratio (word multiply vs field M, port pressure). Paper analysis cannot settle it.

## Access and limits

- I read: Thorup v9 §2.2, §2.3, §3.3–3.5; the Pătraşcu–Thorup introduction; Joye–Tymen Corollary 1; BLS pp. 2–5 and 12–15.
- All were the round-1 local copies, which are untrusted downloads. I read them only with sed and grep; there was no fresh web access.
- I did not read the Carter–Wegman, Dietzfelbinger, Wegman–Carter 1981 or CIOS primary sources.
- No edits, runs, imports or child agents.
- I did not duplicate Sol's or Astra's schedule and chain-expectation work.
