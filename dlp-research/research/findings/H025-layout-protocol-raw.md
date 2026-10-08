# Raw H025 Fable protocol review — reconcile before acceptance

TaskId: node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h025-layout-protocol-fable-20261008-r1

This review predates the independently reviewed O,G,Q initial-input convention;
its counts may omit those comparisons. Raw assertions require root reconciliation.

# H025 signed-layout protocol/cost review (read-only; no runs, edits, children, commits)

Sources read: `hypotheses/H025-signed-layouts.md`, `findings/H024-manygiant-coverage.md` (the file is under `findings/`, not `hypotheses/`), `findings/H024-escape-finite-negative.md`, `experiments/H024/protocol.md` (cost conventions only), `findings/H019-xonly-baseline-screen.md` (wrapper/memory conventions). Modular-origin/coverage mathematics left to Astra. No numerical results below; all numbers are protocol parameters and worst-case enumeration counts derived by hand from the frozen rules.

## 1. Frozen parameters implied by the text (both tested primes)

| | q=73 | q=509 |
|---|---|---|
| h, k, ell, B | 1,1,1, **B=3** | 1,1,1, **B=3** |
| M=floor(sqrt(q/2)) | 6 | 15 |
| 3·ceil(sqrt q), main cap (whole blocks) | 27 pts = 9 blocks | 69 pts = 23 blocks |
| f=4 per-family lengths at cap | (9,6,6,6) | (18,18,18,15) |
| f=3 (control) lengths at cap | (9,9,9) | (23,23,23) |
| Fallback D=ceil(sqrt(2q)); idx 0..ceil(D/2) | D=13; 0..7 | D=32; 0..16 |
| Fallback after whole-block overshoot | 0..8 per family = 18 pts | 0..17 per family = 36 pts |
| A shifts c=D·b² (D=floor(q/17)) | D=4: (0,4,36,50) | D=29: (0,29,261,224) |
| B shifts c=D·b² (D=floor(q/73)) | **D=1**: (1,4,16,64) | D=6: (6,24,96,384) |

Two consequences the proposal does not state: (a) the even-B centered path is **dead code** at both primes (B=3 always; h=2 first occurs at log2 q ≥ 32), so whatever endpoint rule is frozen is untested by this gate; (b) at q=73 the cap can end mid-round (9 blocks over 4 families), which is fine but must be stated as allowed.

## 2. Exact mean / survival sum: correct in form, three fixes needed

The sum `B·(q − covered_before)/q` at each completed block is the exact expected key count under a uniform scalar for a fixed target-independent schedule, provided:

1. **Zero scalar.** k=0 means Q=O, detected at input. Including it is 1/73 ≈ 1.4% of the mass at the small prime, which is a quarter of the 5% margin. Freeze: bitmap over 1..q−1, denominator q−1. (The H024 finding already flags this.)
2. **Integer gate.** With a common denominator the gate is `20·N_cand ≤ 19·N_GWZ` on the integer numerators N = Σ B·(q−1−cov_before) over main and fallback blocks. No floating point.
3. **Fallback charge.** The bitmap union is the right object: fallback block survival = (q−1 − cov)/(q−1) with cov continuing from the main bitmap. Fallback must run its full whole-block range (0..8 or 0..17 per family) whenever σ_cap>0; the only exact early stop anywhere is `cov == q−1` in main (all later terms are zero). Clearing is in record units, not keys: report `σ_cap × cap_records` **separately**, do not fold it into the key sum. Assert bitmap full after fallback; a false assertion is a protocol error (inconclusive), not a result.

Fallback coverage check (hand): round(k/D) ≤ ceil(D/2) for all k<q at both primes (6≤7, 16≤16), so the H019 wrapper's range is sufficient; the enumeration verifies it anyway.

Even-B endpoints (freeze now, untested here): `lo = −floor(B/2)`, `hi = B−1−floor(B/2)`; positive round appends `[hi+1, hi+B]`, negative round `[lo−B, lo−1]`. For B=3 this is −1..1 as written.

## 3. Candidate-pair enumeration budget: proposer's 20853 is an upper envelope; 40/update is uncertified

Independent worst-case count (all six combinations hit the cap; cross-family both signs = t²−ΣL_i², same-family negative pairs counted naively as L(L+1)/2 for every b_i≠0, direct infinity one per nonzero-b point):

| design | q=73 main | q=73 fb | q=509 main | q=509 fb | total |
|---|---:|---:|---:|---:|---:|
| A | 621 | 216 | 4077 | 837 | 5751 |
| B | 675 | 216 | 4266 | 837 | 5994 |
| GWZ-style control | 594 | 216 | 3772 | 837 | 5419 |
| **sum** | | | | | **17164** |

So 20853 ≥ 17164: the candidate count is safely enveloped. The arithmetic 20853·40+50000 = 884120 < 10⁶ is correct, but the margin is 1.13× and depends entirely on two unverified assumptions: ≤40 events per candidate, and ≤50000 for everything else. The second is low if per-point work is not an "update": each new point needs 2(f−1)+1 AP starts (~8–10 events each) plus label and infinity, roughly 100 events per point, and there are ~450 points across six runs (~45k) before any setup/clear. The budget is only safe if the inner loop is cheap. **Admission condition: no per-pair modular inversion and no per-pair label recomputation.** An extended Euclid per pair (~60–150 events) alone would exceed 1M.

## 4. Routine skeleton with per-line charge (this is the certification basis, not infrastructure)

Setup per (design, prime), charged once: for every ordered family pair (i,l), sign ε: `e=b_i−ε·b_l`; if e≡0 record `zero_denominator` else `inv_e` by Euclid; `step[i][l][ε] = ε·s_l·inv_e mod q`. Also `inv2b[i]`, `invb[i]` for b_i≠0. ≤ 2f²+2f ≤ 40 inversions, ≤ ~200 events each → ≤ 8k. Bitmap `first_block[1..q−1]=0`, `channel[k]`, `cov=0`.

```
emit_block(i, lo_new..hi_new):                      # charge at completion
  for j in lo_new..hi_new:
    a = (c_i + j*s_i) mod q                        # 3
    if b_i != 0: mark((-a*invb[i]) mod q, INF)     # 3 + mark
    for l != i, for eps in ±1:                     # 2(f-1) starts
      if no inv_e or family l empty: continue      # 2
      k = inv_e*(eps*(c_l + lo_l*s_l) - a) mod q   # 6
      for r in lo_l..hi_l:                         # per candidate:
        mark(k, CROSS)                             #   <=4
        k += step; if k >= q: k -= q               #   <=3
        (loop inc/compare)                         #   2
    if b_i != 0:                                   # same-family negative, r strictly earlier
      k = -(a + a_i(lo_i))*inv2b mod q; walk r with step -s_i*inv2b   # same per-candidate cost
    append j (update lo_i/hi_i)                    # 2
  cov_after -> numerator += B*(q-1-cov_before); record cov curve
mark(k, ch): if k != 0 and first_block[k]==0: first_block[k]=blk; channel[k]=ch; cov+=1   # <=4
```

Per candidate ≤ 9 under the H018 Meter convention (field/int ops, compares, loop steps, dynamic array accesses charged; fixed tuple reads administrative). Conservative bound I will stand behind: **≤12 per candidate, ≤120 per emitted point, ≤10k setup per design-prime, ≤10 per block, clear = cap records.**

Resulting conservative worst-case totals (every run hits cap, fallback always runs):
- Proposer's primes {73, 509}: 17164·12 + 450·120 + 6·10k + 5k ≈ **330k**; at 16/candidate ≈ 400k. Margin ≥ 2.5×.
- The static per-line count of the implemented inner loop must be reviewed before the first run. If it exceeds 16 events per candidate, do not run; fix the loop.

## 5. Memory and the unknown full-EC cost

- Probe memory is O(q) small integers; irrelevant to the solver claim.
- Solver peak records under this wrapper: `max(cap_points, fallback_points) + f·(centers k + offsets ell + stride point + base point) + scratch` = at q=509: max(69,36) + 4·4 full points + scratch. Note the cap 3·ceil(sqrt q) is **~2.1× the proved two-family table** (≈ sqrt(2q)+O(B) records). The three designs share the cap, so candidate-vs-control is equal-cap; it is **not** an equal-memory comparison against the proved 2sqrt(2)/3 baseline. Label it so.
- Full EC setup is not measured by this probe and dominates at these sizes. Per family: stride point, b_i·Q, c_i·G, one center, one offset. Control: strides 1, M, −(M+1) cost one scalar mult plus one add; b_iQ is Q, 2Q; c=0. Candidate A adds three generic scalar mults (c_i·G, since D·b_i² mod q is full-size) and small multiples 3Q, 7Q; B adds four. That is roughly 3–4·(1.5·log2 q) extra group operations ≈ 30–55 at q∈{73,509}, versus expected key counts on the order of 8–20. **At these primes arithmetic is setup-dominated; a key-count difference is not an arithmetic difference.** Per-key cost at h=1 is `S + (4/3)M + (2/3)I` (from H019 Cx(1,1)), inversion-dominated, and it is not identical across f if centers are batch-inverted across families (k_eff=f). Any later full-cost comparison must freeze batching rules; the key gate does not.

## 6. Is the 5% key gate a meaningful scoped falsifier?

As a falsifier of **"this exact finite protocol saves ≥5% keys over the GWZ-style control at q=73 and q=509"**: yes, exact, integer-only, cheap. As evidence about the asymptotic constant or the shift mechanism, in either direction: **no**, for four quantifiable reasons.

1. **Block quantization.** B=3 and E is a sum of ~3–6 terms at q=73; 5% of E is ~0.4 keys, well under one block. First-block coverage order (which family goes first, whether its b is zero) moves E by a third of a block by itself.
2. **Linear terms.** Same-family negative matches and direct infinity contribute ≤ 2t to coverage versus (1−1/f)t² cross-family. At the completion scale t ≈ sqrt(q/(1−1/f)), their share is 2/((1−1/f)t): ≈ 25% at q=73, ≈ 10% at q=509, ≈ 7% at q≈1000. It only drops below 1% for q > ~5·10⁴, where t² enumeration exceeds 1M events. **No prime that fits the 1M ledger makes the linear term smaller than the 5% margin.** The designs have unequal numbers of nonzero-b families (2 of 3 vs 3 of 4 vs 4 of 4), so this term is a systematic bias, not noise.
3. **Zero scalar** (1.4% at q=73), fixed by §2.
4. **q=73 specifically**: B's shift D=1, and the chart "finite distance" terms (|Δ|+|v|)/(|e|q) exceed 1 since v ranges to ~9·16 > q. Whatever Astra concludes about origin separation, no such argument applies at q=73; it can only test code correctness.

What the same enumeration gives for free and does target the claimed mechanism ("separate collision channels whose origins coincide"): tag each first discovery with its channel and report, per completed block, the cross-channel efficiency
$$\rho(t)=\frac{\text{cov}_{\text{cross}}(t)}{t^2-\sum_i L_i^2}\in[0,1],$$
the attained fraction of the counting ceiling, i.e. one minus the coincidence loss. The mechanism predicts ρ_A, ρ_B ≥ ρ_control at matched t before saturation (t ≲ 0.8·sqrt q). This is still finite and still subject to wrap effects, but it isolates the quantity the shifts are supposed to improve from block order, linear terms and setup. Cost: one extra array write per first discovery.

## 7. Cheapest adjusted fixed protocol (single recommendation, before any test)

Keep the proposer's wrapper (block rule, family order, cap rule, clearing, signed two-family fallback with overshoot, no main/fallback cross-pairs) and change only:

1. Primes **{509, 1009}** instead of {73, 509}. Rationale: §6 item 4; at q=1009, h=1, B=3, cap 96 pts = 32 blocks (f=4: exactly 8 rounds, (24,24,24,24); control (32,32,32)), fallback D=45, idx 0..23 = 8 whole blocks per family, 48 pts. Worst-case candidates: A 9360, B 9684, control 8740 → with q=509: **42410 total**. Conservative events at ≤12/candidate: 42410·12 + 747·120 + 60k + 5k ≈ **665k**; at 16/candidate ≈ 835k. Still one global 1M-event/60 s cap, exhaustion inconclusive, all partial records retained. Precondition: static inner-loop count ≤16 per candidate; if not met, do not run.
2. Exclude k=0; integer gate `20·N_cand ≤ 19·N_control` on **both** primes, fallback included, clearing reported separately in record units.
3. Channel tagging and ρ(t) per block for all three designs, retained in full regardless of outcome, together with: cov curve, main stop block (cov==q−1 or cap), σ_cap, zero-denominator counts, candidates enumerated, events per phase, bitmap-full-after-fallback assertion.
4. Freeze even-B endpoints as in §2 and state they are untested at h=1.
5. Label the control "GWZ-style b=(0,1,2), s=(1,M,−(M+1)) under this wrapper", not GWZ's algorithm or its reported .89–.92 constant.

## 8. Admission conditions (all required)

- Precomputed inverses/steps; no per-pair inversion or label recomputation; static per-line event count of the implemented loop reviewed and ≤16/candidate before the first run.
- Only early stop: `cov == q−1` in main. Fallback always run to its full whole-block range when σ_cap>0. No bound-based inter-design early stop (unnecessary at this budget; if ever used, it must be the monotone pair L_n = partial sum, U_n = L_n + σ_n·(remaining main keys + fallback keys), decide only when L_cand > .95·U_ctrl or U_cand ≤ .95·L_ctrl).
- Declared outcome semantics written before running: pass/fail refer to the finite key-count protocol at the two primes only. No asymptotic, equal-memory-vs-proved-baseline, arithmetic, full-solver or hardness claim follows from either outcome. Failing does not reject the family; passing requires larger independent validation plus complete EC arithmetic/memory accounting as the proposal already says.
- Peak-record formula and the 2.1× cap-vs-two-family-table ratio reported with the result.
- H018 Meter/prime_trial conventions as in the H024 protocol; -B, external timeout; protocol and source hashes retained with output.

Not repeated here, per instruction: the rejected claims that small tests settle a 32-bit discrepancy or that a per-design 1M budget was certified. Nothing in this review asserts that a key gain equals a full-solver improvement; §5 argues the opposite at these sizes.
