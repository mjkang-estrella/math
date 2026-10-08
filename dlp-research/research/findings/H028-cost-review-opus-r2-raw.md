# H028 cost review r2 — raw Claude Opus delivery

2026-10-08. Retained verbatim. Reconciled scope and protocol decisions are authoritative in H028-uniform-fibre-bound.md and the task register. In particular the unexpanded all-points/symbolic diagnostic does not fit a justified1M budget; no run under that estimate is accepted.

I've read all four documents. Now writing the review; no experiments run.

# H028 provisional-key review (replacement round, read-only)

**Verdict: conditional GO** for a small fixed-synthetic diagnostic that checks correctness and the fibre identity. **NO-GO** on any performance or timing claim from it. Verified improvement: **NONE**.

Sources read in full: `hypotheses/H028-provisional-key-candidate.md`, `findings/H028-provisional-key-preflight.md`, `findings/H027-compact-trace-construction.md`, `findings/H019-xonly-baseline-screen.md`, plus the fixture table in `findings/H024-escape-finite-negative.md`. I ran nothing, edited nothing, fetched no sources and started no child tasks.

## 1. Checks that pass

- **h laws.** From H027, `a(Q+R) = aQ + aR − q·λ` and `a(−Q) = −aQ`. Since q≠p, q is invertible in Fp, so `h = a/q` gives `h(P+R) = hP + hR − λ(P,R)` and `h(−P) = −hP`. Signs match for the pair C±J: `h(C±J) = hC ± hJ − λ±`.
- **Uniqueness.** Two functions satisfying this law differ by an additive Fp-valued map on a group of order q, which is zero. So h is well-defined.
- **Block costs.** `Kx = (ℓ+1)·I + 3(ℓ+1)(k−1)·M + 2kℓ·M + 2k·M + k(2ℓ+1)·S`, which gives `(ℓ+1)[I + (5k−3)M] + k(2ℓ+1)S`. The h-key version keeps all the slope multiplications, keeps the center advances (x needs S, y needs M), and updates h with additions only. So `Kh = … + kS`, saving 2kℓ·S per block. In the limit that is 2.5M per key (plus a residual S/(2ℓ+1)) against 2.5M+S. The generation-only ratio of 2.5/3.3 at S/M = 0.8 is correct. In H019's units, B would drop from 0.536 to about 0.406, but only within the arithmetic model.
- **Repaired recovery step.** `λ± = hC ± hJ − h(C±J)` and `x = λ² − xC − xJ`: one S, no inversion and no M. Correct.
- **Sign handling.** If hU = hV ≠ 0 and x matches, then V = U. If hV = −hU ≠ 0, then V = −U. If h = 0, both scalar signs must be checked. Correct.
- **Randomization.** For fixed s, V is uniform because r is uniform, so U and V are independent. Linearity of expectation is all that's needed.
- **False-comparison formula and its reconciliation.**
  - The sum over U≠O of `d_{c(U)}`, minus 2(q−1), equals `S2 − 2(q−1)`.
  - The root's all-point version adds exactly `d0 = c0`, which counts the comparisons against giant O.
  - `S2 = 2·M2 − c0²` is correct.
  - ρ ≥ 1 holds because every nonempty canonical bucket contains a distinct pair {P, −P} (q is odd).

## 2. Main new point: ρ ≤ 3 follows directly from the h law

This is my own derivation and needs an independent check. It turns the "UNPROVED and UNMEASURED" premise into a short lemma.

Count `M2 = #{(U,V) : U,V ≠ O, hU = hV}` by writing V = U + P:

- **P = O:** this gives q−1 pairs.
- **P ≠ O:** then U ∉ {O, −P}, so the addition law applies, including the tangent case U = P. So hV = hU exactly when **λ(P,U) = h(P)**. That means U lies on the non-vertical line through P with slope h(P). That line meets E in a degree-3 divisor containing P, so the remaining degree 2 allows at most 2 solutions U. U = P counts only when the line is tangent at P.

Hence `M2 = (q−1) + Σ_{P≠O} N(P)` with each N(P) ∈ {0,1,2}. So M2 ≤ 3(q−1), S2 ≤ 6(q−1) and **ρ ≤ 3** for every prime-order curve with q≠p.

Consequences:

- **Expected false comparisons at full caps:** at most 4IJ/q. With H019 prefixes (IJ ≈ q/2) that is about 2 per solve, for every input, because the expectation is over the paid s and r. The extra giant-O term is at most IJ·c0/(q(q−1)), where c0 ≤ √(3(q−1)). That is negligible.
- **Heuristic value:** N(P) is 2 or 0 depending on whether a quadratic splits, so ρ should be about 2 (just under). That agrees with the random-function model 1 + q/p.
- **Gate type:** this is a sufficient upper bound, not a measurement. The identity also gives the diagnostic an exact equality to check, not just a statistic.

## 3. Hidden costs and simplifications

1. **The archives are unnecessary in the expected-cost regime.** With at most about 2 expected false matches, on any raw key match one can simply verify the candidate scalar(s) by scalar multiplication. Orientation fixes one candidate when h ≠ 0; otherwise try both. That costs O(log q) per false match, so O(log q) expected in total.
   - This drops the (xC, hC) archive, its lifetime rules and the orientation-bit dependency.
   - Records then match H019 exactly: key plus index, optionally one bit.
   - The archive only helps with tail cost (Markov: P[false > t] ≤ 2/t). Its about 2/(2ℓ+1) field elements per key must be charged if it is kept.
2. **Record format must match the comparator.** If the comparator stores truncated x fingerprints, H028 cannot rebuild hSide from a fingerprint, so the one-S recovery no longer applies. Both sides then pay recomputation on fingerprint hits. The comparison must fix the same record format on both sides.
3. **Field additions and canonicalization.** H028 adds about 3–4 extra additions per pair, plus a negation and a fully reduced comparison to compute `min(rep h, rep −h)`. The x-key gets the ± merge for free. These are small against 2S but must be counted.
4. **Setup is cheaper than budgeted.** `h(nG) = n·h(G) − c_{n,G}`, so h(G') and h(rG) come out of the affine sG and rG chains as additions, after one target-independent h(G). The only per-target Miller chain is h(Q), costing O(log q) operations. Done projectively, that is slope fractions plus one inversion. Offsets, BT and DG' are additions on additions already charged in H019.
5. **Scope of the comparator.** The saving is measured against the H019 specialization in short Weierstrass affine form only. The law is model-specific. No claim is made that H019 is the best x-key schedule in the literature.
6. **Real-world cost.** High-memory BSGS is often limited by memory and hashing. Saving about one S per key does not imply a wall-clock gain. That gate needs an equally optimized x-key implementation at nontrivial size, and toy q cannot inform it. A loss at toy size from startup costs also does not reject the mechanism at larger sizes.

## 4. Smallest justified diagnostic (Sol owns the protocol; these are acceptance criteria only)

Use the existing fixtures (p, q) = (59, 73), (101, 103), (251, 271), (8191, 8053). All have q≠p. Enumerating all q points is paid diagnostic work, not production advice.

- **(a) Independent h check.**
  - At q = 73 and 103, build the Miller function explicitly and read a_Q from its Laurent expansion at O. This is genuinely independent of the c-recurrence.
  - At all four sizes, compare a binary-chain Miller computation with sequential propagation `h((n+1)G) = h(nG) + h(G) − λ` for every point. This checks independence from the chosen addition chain, which is a weaker test.
  - Check `h(−P) = −h(P)`.
  - Check the addition law on all pairs for q ≤ 271, and on a predeclared sample at q = 8053.
- **(b) Fibre identity.** Compute S2, c0 and M2, and separately ΣN(P) by intersecting each line with E. Require **M2 = (q−1) + ΣN(P) exactly** and ρ ≤ 3. Any violation falsifies either the lemma or the implementation.
- **(c) Exception cases, correctness only.** One fixed-seed paired-block run per fixture with these cases forced: C = ±J, finite tangency, a zero-h bucket, giant O, Q' = O, and an orientation-based single-candidate check. Fixed seeds are correctness cases, not IID performance trials.
- **Budget.** Well within the tentative 1M-event / 60 s cap. Exhausting the cap is inconclusive, with no retuning.

## 5. Open items that make the GO conditional

1. The ρ ≤ 3 lemma (§2) needs independent review before it replaces the "unmeasured premise" in the candidate. The diagnostic in (b) only falsifies it; it cannot prove it.
2. Novelty and prior art are still open. Liao–Zhang §3.1 (normalized EDS provisional keys) and GWZ shared-inverse generation are recorded antecedents. I did not reread either source, and I make no novelty claim.
3. The record format and the archive-versus-verification choice must be fixed identically for both sides before any cost comparison (§3.1–3.2).
4. The full static ledger is still incomplete: additions, canonicalization, hashing and bucket traffic. No complete-work or wall-clock gain is supported. The supported complexity remains square-root.