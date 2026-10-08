# H030 filter/recovery primary-art review — raw, pending reconciliation

2026-10-08. Provider claudeAgent; model claude-opus-5-5.
TaskId node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h030-filter-recovery-priorart-opus-20261008-r1
COMPLETED, result acknowledged. Sources and mathematical extensions below are
reviewer reports pending root/independent checking, not accepted gain or novelty.
No numerical test. Raw finite ratios and new hierarchy assertions need review.

# Review of H030 Card A (index-free filter for signed-BSGS babies): mechanism holds, but the 13× claim, the hash-guarantee claim and the "end of road" claim don't

**Verdict.** I'd keep Card A as a limited, plausible storage construction for the memory-constrained regime. Verified improvement remains **NONE**. Three claims need correcting:

- **The 13× density ratio.** The baseline it's measured against was set too high (≈262 bits/baby instead of ≈140).
- **The "rigorous" hash guarantee.** Plain multiply-shift isn't strong enough for the cuckoo or Bloom false-positive (FP) bounds as stated.
- **Novelty.** The sublinear resolution step is already in public code (keyhunt). A multi-level version of it gets **O(1)** bits/baby, so Card A's O(log log q) is not "the end of the road", and Card C consequence (2) falls.

Everything below is paper-level; I ran no numerical test and edited no files.

## Sources checked

| Source | Access | What it supports |
|---|---|---|
| Fan, Andersen, Kaminsky, Mitzenmacher, *Cuckoo Filter* (CoNEXT 2014), full text | OK | FP ≤ 2·(slots per bucket)/2^f, so f ≥ log₂(1/ε)+log₂(2·slots). Bits/item (log₂(1/ε)+3)/α, or +2 with semi-sort, α≈95.5%. The info-theoretic floor of log₂(1/ε) bits is stated there. **Minimum fingerprint f = Ω(log n/b)** (b = slots per bucket here) comes from a construction-failure lower bound. That bound "assumes hashing the fingerprints is collision-free". They say "how much independence is required" is **open**, and the load factors are **empirical**. |
| Eppstein, *Cuckoo Filter: Simplification and Analysis* (arXiv 1604.06067) | OK (grep of the text) | Proves f = Ω((log n)/b) is necessary and sufficient, under "the unrealistic assumption of a uniformly random hash function". |
| Thorup, *High Speed Hashing for Integers and Strings* (arXiv 1504.06804) | OK | Multiply-shift is **2-approximately universal**: Pr[h(x)=h(y)] ≤ 2/2^ℓ. It is *not* strongly universal (Exercise 3.4). Strongly universal options are multiply-add-shift with w̄ ≥ w+ℓ−1, or vector multiply-shift (§3.3–3.4). |
| Bender et al., *Don't Thrash* (quotient filter, VLDB 2012) | OK | (r+3)/α bits per slot. FP only on full p-bit hash collisions, ≤ n/2^p ≤ 2^-r. Their formula assumes uniform hashing. |
| Bernstein–Lange, *Computing small discrete logarithms faster* (2012), §5 | eprint link returned HTML; cr.yp.to copy OK | Hash table entries down to "a few bits per entry" with sorted-hash compression, plus false-alarm accounting. Known prior art for fingerprint compression. |
| keyhunt (albertobsd), `keyhunt.cpp` main | OK, code read | Details below. |
| Putze–Sanders–Singler, Cleary 1984, Pagh–Pagh–Rao, Corrigan-Gibbs–Kogan, Pătraşcu–Thorup, XOR/ribbon filters | **Not accessed** | Anything I attribute to these is from memory and unverified. |

**keyhunt detail.** Signed x-only BSGS with stride 2m, three Bloom filters at ε=10⁻⁶ holding m, m/32 and m/1024 babies, and **no index at level 1**. On a level-1 hit, `bsgs_secondcheck` runs ≤32 sub-giant steps against the level-2 Bloom. `bsgs_thirdcheck` then runs ≤32 steps against the level-3 Bloom plus a sorted table of m/1024 entries (6-byte truncated x + 8-byte index), and tries ±(j+1). That is ≈29.8 bits/baby (my arithmetic). The code is in `keyhunt.cpp` from at least 2023-04-25; I didn't check the history of the earlier `keyhunt.c`.

## Is 2-universal multiply-shift enough?

- **For an equality filter: yes, with one extra bit.** In a quotient filter or Cleary compact hash, a false positive requires a full hash collision. The union bound over the b stored keys gives ≤ 2b/2^p. For 256-bit x, use vector multiply-shift.
  - Construction is in place and deterministic: it always succeeds and never needs a rebuild.
  - Only the probe *time* (cluster length) depends on hash quality. That is heuristic under 2-wise hashing; constant independence is needed for proven O(1) (from memory, unverified).
- **For the cuckoo filter: no.** An FP for a query x means some stored y has fp(y)=fp(x) and i1(y) ∈ {i1(x), i1(x)⊕H(fp(x))}. The second event is not a hash equality, so plain universality says nothing about it.
  - With a **strongly universal** (i1, fp) and a separate H, the bound is ≤ 2b/(m·2^f) = 8α/2^f for 4-slot buckets. That is rigorous, but conditional on construction succeeding: ≤ ε/Pr[success] when you rebuild on failure.
  - Construction success has no proof under limited independence.
  - A rebuild with a new seed **can't be done from fingerprints**. It means regenerating all b babies at a cost of b·c_gen per failure.
- **For Bloom / blocked Bloom: no.** The (1−e^{−kn/m})^k formula needs joint independence of the k probes across all keys. Pairwise independence only gives a single-probe-style bound. Treat the Bloom FP rate as heuristic.
- **Adaptive queries.** The giant queries are fixed by Q and the public schedule. If the seed is independent of Q, E[#FP] ≤ g·ε follows by linearity alone; it bounds the mean only, not the variance.
  - If one table is reused across many targets under a known seed, each target needs re-randomisation (Q+rG with fresh r). Otherwise an adversarially chosen Q can force false positives.

## Corrections to Card A

1. **Baseline bits are overstated.** The repo's own H020 Fable review already gives the competent hash-and-verify baseline at ≈0.5·log₂q + O(log log q). With quotienting, position encodes about log₂b of the key bits. So the baseline is ≈ log₂b + log₂(1/ε) + O(1): roughly 140 / 75 / 44 bits at log₂q = 256 / 128 / 64, not 262 / 130 / 66.
2. **The FP scan must be priced at worst case, over both signs.** Card A's resolution cost V is quoted from the true-hit average.
   - With a signed sub-table the sub-search must scan both signs, P*∓t(2β+1)G. A false positive never stops early, so it costs **≈ b/β = b^δ** sub-giants. A true hit averages about half that.
   - "Unbatched, ≈4 keys each" contradicts V ≈ 1.06·b^δ keys. At 4 keys each, V_FP ≈ 4·b^δ, which costs about 2 more bits/baby.
   - V ≈ b^δ keys is reachable only by precomputing the b^δ multiples t(2β+1)G and batching the inversions. That is cheap, but it has to be stated.
   - I don't assign a price to the inversion I.
3. **The cuckoo construction bound binds at 256 bits.** Fan's lower bound with 4-slot buckets at α≈0.955 needs n·(7.64/2^f)^8/9! < 1. At n=2^128 that means **f ≳ 17**, above the 14.1 the FP target needs. So the 256-bit row is ≈17/0.955 + 1.9 (sub-table) ≈ **19.7** bits, the top of the claimed range. At 2^62 and 2^30 the bound doesn't bind. A quotient filter or a static filter avoids the issue.
4. **Corrected density ratios** (my arithmetic; assumes one batched sub-addition ≈ 1 key-equivalent and a 10% FP budget): about **2.9× / 4.7× / 7×** at log₂q = 64 / 128 / 256. That is against the quotiented truncated-key-plus-index baseline. **The 13× claim and the W/√q table** (the 48√q baseline crossover becomes ≈25√q) should be retracted.
5. **Construction cost.** Bloom, quotient and cuckoo filters build streaming and in place. Sorted-hash or Elias–Fano layouts need either peak storage near the baseline's size, or P passes that each regenerate all babies (P·b·c_gen). The exact sub-table costs β inserts at c_tab each, but no extra generation, since its babies are the first β of the stream. "≲1 M per baby" is unpriced, so keep it as a symbol c_ins.

## The capable baseline: multi-level hierarchy, O(1) bits

Recurse keyhunt's structure with ratio r per level and L ≈ ⌈log_r(log₂p + log₂b)⌉ levels, ending in an exact table.

- **FP cost stays constant.** A false positive at any level stays false at every lower level: if R_t = ±vG with v ≤ b_{ℓ+1}, then P* would lie truly in range. So E[V_FP] ≤ 2r(c_add + c_probe) when ε_ℓ ≤ 1/(2r) for ℓ ≥ 2.
- **Bits/baby ≈ bits(ε₁) + O(log r / r) + ≤1, independent of q.** Here ε₁ ≈ 0.1/(2r). A true hit costs L·r sub-steps, once.
- **At r=32 that is ≈ 15–17 bits/baby with a quotient filter, at every size.**
- **No conflict with Corrigan-Gibbs–Kogan.** Total advice is still Θ(b) bits, so ST² ≳ b holds (I haven't verified their interval variant).

Consequences:

- Card A is the L=1 special case. Its O(log log q) is beaten asymptotically, though only by a few bits at these sizes.
- Card C's "within a small constant of the end of this road" and the floor "≈ log₂(V/c_key)" are wrong as stated. Astra owns Card C's algebra; this should go to them.
- On novelty: the measured delta should be taken against a *tuned* hierarchy. Card A against keyhunt's defaults (29.8 bits, Bloom at 10⁻⁶) shows ≈1.5×, and that gain comes from choosing ε and the filter type, which the baseline can also do. I am not saying the measured benefit is zero; that is what the ledger has to show.

## Construction I'd accept (limited)

Signed x-only BSGS with:

- an index-free **quotient filter** (or Cleary compact hash) over the babies, hashed with vector multiply-shift;
- one or more resolution levels (an exact sub-table, or recursive filters);
- batched sub-giants with precomputed multiples;
- standard final verification.

Recovery is exact and there are no false negatives. Expected FP work is ≤ g·2b/2^p·V_FP, rigorous under approximate universality.

**Assumptions it needs:**
- the seed is independent of the targets (re-randomise if the table is reused);
- the memory-constrained regime counts for the metric (coordinator ruling);
- full-point lift of the giant costs about 3 keys (unverified);
- probe time is heuristic;
- no hardware prices.

## Cheapest decisive paper ledger

At log₂q ∈ {64, 128, 256} and the same bit budget W, write out:

W_total = b(c_gen + c_ins) + R·b·c_gen [cuckoo only] + β·c_tab + g(c_gen + c_probe) + g·ε·V_FP + V_true + c_verify

- **Use:** V_FP at worst case over both signs, with ε at its rigorous value for each filter. Use g = q/(4b) on average and also show q/(2b) worst case.
- **Columns:** (a) quotiented key+index; (b) keyhunt defaults; (c) tuned hierarchy with r and L optimised; (d) Card A, cuckoo and quotient-filter variants.
- **Kill or retire:** retire Card A as distinct if (d) doesn't beat (c) by at least 1 bit/baby at matched W_total. Report (d) against (a) as a known-class constant only.
- **Numerical run:** only after that, ≤1M events at q≈2^20 to check FP counts and exact recovery.
