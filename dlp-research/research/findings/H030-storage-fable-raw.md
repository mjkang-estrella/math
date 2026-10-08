# H030 Factory Fable storage proposal — UNREVIEWED raw delivery

2026-10-08. Provider acpRegistry_factory_droid, model claude-fable-5.1.
TaskId node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h030-storage-tradeoffs-fable-20261008-r1
Terminal COMPLETED, no pending children. Root retains this as a proposal, not
acceptance of its numerical constants, hash guarantees, novelty or universal
class-optimality claims. Independent review follows; no numerical run admitted.

# H030 external-memory / high-memory lens: proposal memo

**Bottom line.** Verified improvement remains **NONE**; generic exponent 1/2 unchanged. No storage mechanism changes the record-count tradeoff of meet-in-the-middle; I give a short exact counting argument (Card C) showing signed x-only BSGS and GWZ interleaving are already optimal within the whole "stored fixed-log records + dictionary lookups" class, so sorting/hashing/staging cannot move it. What storage organization *can* move is **bits per record**, and there I propose one concrete construction (Card A) that reaches roughly 15–20 bits per baby at 256-bit sizes with exact index recovery, against ~260 for the competent truncated-key-plus-index table. That shifts the entire memory-constrained tradeoff curve left by a factor ≈ 13 in storage bits (≈ 4 at 64-bit synthetic sizes), including moving the rho crossover from ≈ 48√q bits to ≈ 4√q bits. It is a constant-factor, regime-restricted change, zero at unconstrained memory, and still astronomically infeasible at 256 bits (≈ 2^130 bits). Card B is a quantified rho+table "bridge" with at most ~6 % heuristic gain before probe costs. Card D is the external sort-merge baseline, included only so "memory-constrained" is defined in bytes on any medium.

## Comparator ledger used (all from repo-accepted findings)

- Negation rho, batched affine: ≈ 0.886√q additions at (5+s)M, s=S/M. At s=0.8: 5.14 M√q heuristic leading term (H013, H029 model).
- Memory-bounded signed x-only BSGS with b stored baby abscissae, stride 2b+1: average b + q/(4b) keys at Cx → 2.5M+S (H019, H020 Grok Card 2). Beats rho iff b/√q ∈ (0.183, 1.37) at s=0.8.
- GWZ interleaved, both sides stored (~1.41√q records): (2√2/3)(2.5+s)√q ≈ 3.11 M√q (H019 screen).
- Competent memory-constrained storage per baby: truncated key (log₂b + ~6 bits) + index (log₂b) with recompute-verify, or quotiented compact hash: both ≈ log₂q + O(1) bits. Full x + index ≈ 1.5 log₂q. (H020 disposition left "static packed table" and "recovering a matching index is a different task" explicitly open.)

## Card A — Index-free baby table with sublinear exact index recovery

**Public operation.** Standard signed x-only BSGS (H019 block generation unchanged). Store for each baby x(iG), 1≤i≤b, only a short fingerprint in an approximate-membership structure with false-positive rate ε (cuckoo filter or blocked Bloom; both build in place, streaming, no extra construction memory). Store **no index and no key**. Additionally build a tiny exact sub-table of x(uG), u ≤ β = b^{1−δ}, with full x and u. Giant query x*: probe filter. On a pass, recover the full giant point (one extra addition from its block center and offset, ≈3 keys), then run an interval BSGS on [1,b] against the sub-table: ≈ b^δ/4 sub-giant full additions (unbatched inversion, ≈4 keys each). An exact x match in the sub-table gives i; one true hit per run plus the usual final scalar-multiplication check.

**Recovery is exact.** The filter never loses a true baby (no false negatives); the sub-table stores full x so the recovered i is exact; the final verification is the standard one. Only false positives cost work, and they are budgeted.

**Bit ledger.** Per-FP resolution cost V ≈ 3 + 1.06·b^δ keys. Budget g·ε·V ≤ 0.1·g keys ⟹ ε ≤ 0.1/V. Bits per baby ≈ (log₂(1/ε)+3)/0.95 (cuckoo, 4-way, 95 % load) or ≈1.5·log₂(1/ε)+2 (blocked Bloom), plus the sub-table's b^{1−δ}(log₂p + log₂b) bits amortized over b. Optimizing δ gives bits ≈ 1.5·log₂log₂q + O(1), i.e. asymptotically O(log log q) per baby. Finite values:

| log₂q | b | δ | V (keys) | ε | bits/baby (cuckoo, incl. sub-table) | baseline bits (trunc. key + index) | density ratio |
|---|---|---|---|---|---|---|---|
| 64 | 2^30 | 0.20 | ≈35 | 2^-8.5 | ≈14–17 | ≈66 | ≈4–5× |
| 128 | 2^62 | 0.10 | ≈95 | 2^-9.9 | ≈17–20 | ≈130 | ≈7× |
| 256 | 2^128 | 0.06 | ≈220 | 2^-11.1 | ≈15–20 | ≈262 | ≈13× |

Versus a fingerprint-only table with *linear* replay (ε ≈ 1/b, hence ≥ log₂b + 3 bits), the ratio is still ≈ 7× at 256 bits. The whole gain comes from making index recovery cost b^δ instead of b or storing log₂b bits; the fingerprint only has to be long enough to make a b^δ-cost resolution rare.

**Complete-work effect (s=0.8, log₂q=256, 10 % FP budget on the giant side, units M√q).** Storage W in bits per √q:

| W/√q bits | rho | baseline BSGS | Card A BSGS |
|---|---|---|---|
| 2 | 5.14 | ≫ | 9.0 |
| 4 | 5.14 | ≫ | 5.0 (crossover) |
| 6 | 5.14 | ≫ | 3.9 |
| ≥10 | 5.14 | ≫ | 3.46 plateau (θ=0.52) |
| 48 | 5.14 | 5.1 (crossover) | 3.46 |
| 131 | 5.14 | 3.30 | 3.46 |
| 370 | 5.14 | 3.11 (GWZ) | ≈3.3 (GWZ sides both compressed, each with its own interval resolution; ≈27√q bits) |

So the tradeoff curve shifts left ≈ 13× in storage; the arithmetic saved is real (fewer giant keys at fixed storage), not bandwidth. Bandwidth per giant: 1–2 cache-line probes, same order as the baseline hash probe. Construction: b in-place inserts, a few tens of word ops plus memory latency each, ≲ 1 M-equivalent per baby; small next to 3.3 M generation and negligible in the giant-dominated regime. Hash: a 2-universal multiply-shift on the canonical integer x gives rigorous pairwise-independent fingerprints, so E[FP] ≤ ε per fixed query holds without a random-oracle assumption; cuckoo insertion success and rebuild-on-failure remain heuristic and paid.

**Gain source.** Pure memory density. Zero change in per-key arithmetic, coverage constant, exponent, or at any storage ≥ √q/2 records. At 256 bits the crossover storage is still ≈ 4·2^128 bits, so the full-size single-target work estimate is unchanged (rho).

**Prior art.** Read in-repo this session: H020 Grok Card 3 (fingerprint + anchors, linear recompute, concluded Θ(log q) bits/baby, which Card A refutes constructively), H020 disposition (noted a 1/log q FP rate would give log log q bits but no index-recovery construction), H004/H028 (keyhunt stores truncated keys plus indices; GWZ). From memory, unverified this session: Bloom 1970; Putze–Sanders–Singler blocked Bloom 2007; Fan–Andersen–Kaminsky–Mitzenmacher cuckoo filter 2014; Dietzfelbinger–Pagh 2008 retrieval; Cleary 1984 compact hashing; Bernstein–Lange 2012 "small discrete logarithms" (truncated DP table entries with recompute-verify); hobbyist BSGS implementations using fingerprint-only tables with linear replay. I cannot attribute the sublinear interval-DLP resolution step; treat its novelty as unverified, and if the coordinator judges it a standard data-structure trick the baseline must receive it and the gain is zero by rule.

**Unsupported assumptions.** (1) The competent baseline stores ≈ log₂q bits/baby; (2) the memory-constrained regime (storage below √q/2 records) is one the main metric cares about; (3) cuckoo/Bloom construction and FP behaviour under a 2-universal hash (FP expectation is rigorous, construction success heuristic).

**Cheapest decisive falsifier (paper, no curve).** Write the exact bit ledger for the three baselines and Card A at log₂q ∈ {64,128,256} with the matched 10 % FP budget and the sub-table charged; compute W(b) = b(c_gen + c_build) + g(c_gen + c_probe) + gεV at fixed storage. Kill if density ratio < 2 after build cost, or if the coordinator rules the regime outside the metric. Only if it survives: one ≤1M-event synthetic run at q ≈ 2^20, b ≈ 2^8, fixed seeds, counting FP events and confirming exact recovery; that checks the FP law, not complete work.

## Card B — rho with a cheap progression table (quantified "bridge")

**Operation.** Standard negation rho with mixed (G,Q) jumps and DP handling, plus one filter probe per step against a Card A table of λ√q baby abscissae. A hit X_t = ±iG with Q-coefficient c≠0 solves k directly.

**Heuristic law.** Under the random-map model the table channel adds hazard 2b/q per fresh point, so P(T>t) = exp(−t²/q − 2bt/q) and
$$E[T]/\sqrt q = e^{\lambda^2}\tfrac{\sqrt\pi}{2}\,\mathrm{erfc}(\lambda),\qquad \text{total} = r\lambda + e^{\lambda^2}\tfrac{\sqrt\pi}{2}\mathrm{erfc}(\lambda),\quad r=\tfrac{2.5+s}{5+s}.$$
Optimum at 2λg(λ) = 1−r. At s=0.8 (r=0.569): λ=0.105 → 0.85 (−4 % vs 0.886), λ=0.184 → 0.833 (−6 %), λ=0.316 → 0.823, but BSGS (Card A) is already at 3.9 M√q there versus 4.77. The hybrid's niche is W ∈ (≈1, ≈5)√q bits with ≤ 6 % gain **before** probe cost.

**Gain source and matched baseline.** Same structure as Bernstein–Lange 2012 single-target precomputation (from memory: f = λ + g(λ) is monotone, so no single-target gain); the only difference is precomputed points cost r < 1 because they are a progression. Baseline: rho at the same storage and Card A BSGS.

**Unsupported assumptions.** Fresh-uniform hazard for walk points; one random probe per step priced at ≲ 0.35 M (6 % of a 5.8 M step). I will not quote hardware; this is the paper kill gate: if c_probe > 0.35 M per step, the card is dead. Also pays table build λ√q·3.3 M (included above) and FP resolution (10 % of the table channel, not the rho steps).

**Cheapest falsifier.** The formula plus a priced probe. No experiment warranted unless probe cost is accepted below the gate.

## Card C — Scoped negative: the record tradeoff is already optimal in its class

**Class 𝒞.** Any algorithm whose stored records certify ≤ c_s points of known form ε_rQ + α_rG, whose queries are points of the same form, and which gains information only from equality between a query and a certified point (implicitly via a dictionary or explicitly via recomputation). Each equality can certify at most c scalars (c=2 for x-only ±). This covers every sorting, hashing, compression, anchoring, staging, and external-memory variant of BSGS/MITM, and is not a generic-group assumption: coordinate tricks that keep this structure are inside it.

**Bound.** If by time t the algorithm has generated t points split into f Q-coefficient classes, implicit comparisons ≤ (1−1/f)t²/2, so P(success ≤ t) ≤ (1−1/f)t²/q and
$$E[T] \ge \tfrac{2}{3\sqrt{1-1/f}}\sqrt q - O(1).$$
For f=2 this is exactly 2√2/3·√q: **GWZ interleaving is optimal within 𝒞 for two classes**, and memory-bounded signed BSGS's q/(4b) is exact for fixed b. The f>2 floors are H024's; they are a coverage program (other roles), not a storage one.

**Consequences for this lens.** (1) Storage organization cannot change record-count work; only bits per record (Card A) or leaving 𝒞 through coalescence (walker-dynamics role) can. (2) Bits per record have a floor ≈ log₂(V/c_key) + O(1), where V is the cost to recover an index from a confirmed x*; Card A lowers V to b^δ with a b^{1−δ} sub-table, giving O(log log q). Going to O(1) bits with O(1) resolution would be an interval-DLP-with-preprocessing oracle (advice o(b) bits, O(1) online), against the Corrigan-Gibbs–Kogan ST² ≳ N type bound (from memory; interval variant not verified). So Card A is within a small constant of the end of this road.

This is a class-restricted counting result, not an impossibility for coordinate-aware methods, and it is paper mathematics I checked by hand against the repo's accepted constants (0.943, q/(4b), H024 floors).

## Card D — Baseline note, not a discovery: external sort-merge

With RAM R records and total storage D records, batch giants R at a time, sort, and merge against the sequentially stored table: EC arithmetic equals a storage-D BSGS; extra cost is bandwidth (g/R)·D sequential record reads plus g·log R sorting. The binding resource is bytes on any medium, not RAM, which is why Card A is stated in bits. This is known practice (HAC-style sorted tables; W004/W009 in repo) and must be the comparator for any "memory-constrained" claim.

## Wave-report items

- Best supported work: unchanged (rho at low storage; GWZ x-only interleaving at √q storage), with the memory-constrained BSGS curve now provably exact within class 𝒞.
- Verified improvement: **NONE**.
- Hypothesis offered: Card A, a constant-factor (≈ log q / 20) storage shift of the memory-constrained tradeoff curve with exact recovery; Card B as a ≤ 6 % bridge contingent on probe cost.
- Evidence against: zero effect at unconstrained memory and at full size; novelty of the sublinear-resolution step unverified; if judged standard, gain is zero by rule.
- Next decision-changing step: the paper bit/work ledger for Card A with the matched FP budget and build cost; no numerical run or Lean work justified before that.
