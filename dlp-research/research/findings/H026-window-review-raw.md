# H026 window conversion: raw independent review

Status: RAW; root accepts only separately reconciled statements. In particular the p_s=0 assertion conflicts with delta=0 anchor self-matches, and the claimed two-sided <=2p_s bound needs an additional symmetry not supplied. Calibration confidence/cost and character-theorem closures are not accepted from this report alone.

TaskId: node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h026-window-conversion-review-opus-20261008-r1
Provider: claudeAgent; model: claude-opus-5-5. Completed and read 2026-10-08.

I read §0, Card 1, the dedup table and the summary of `findings/H026-information-fable-raw.md`, plus the accepted C1 section of `findings/H019-information-disposition.md`. Nothing was run or edited. Fable's outcome stands: **no H was supplied and no gain is supported.** Card 1 as written is not an exact conversion, and its gate is not sufficient. Corrected versions follow.

## 1. Exact conversion for one fixed table

**Setup.**
- Table offset is `s`, with `M = ⌈q/Δ⌉` anchors at `a_i = s + iΔ`. Because `q` is prime, `Δ ∤ q`, so one block is short.
- `β(m)` is the anchor whose window `[a_i, a_i+Δ)` contains `m`.
- `π_b = Pr_m[H(P_m)=b]` is the query distribution over buckets.
- `N_b(s)` is the number of anchors in bucket `b`.

**True success probability (one-sided search, δ∈[0,Δ)):**

  `p_s = (1/q)·#{m∈Z_q : H(P_m) = H(P_{a_β(m)})}`

- If you search |δ|<Δ against every anchor in the bucket, the next anchor `a_{β(m)+1}` also covers `m`. Then `p_s ≤ p_s^(2) ≤ 2p_s`, and each local search costs about `√(2Δ)`.
- Retries `Q ← Q+[r]G` need a fresh uniform `r`, costing about `1.5·log₂q` group operations. With that, attempts are iid Bernoulli(`p_s`). Cheap steps like `Q+G` give correlated attempts, because neighbouring `m` fall in the same block.
- By Wald's identity, expected online cost is `(c_rand + c_H + ν_s·c_loc)/p_s`, where `ν_s = Σ_b π_b N_b(s)` is the expected number of anchors per attempt.
- Preprocessing is `M(1+c_H)`, plus sorting, plus a `√Δ` baby table. Memory is `M + √Δ`.
- You need an attempt cap with a fallback to rho. If `p_s = 0`, which can happen for a fixed `s`, "exact, only costs time" otherwise never terminates.

**Grid vs. all-origin.** Let `ε⁽⁰⁾` be Pr over `n∈Z_q`, `δ∈[0,Δ)` (δ=0 included). The card's ε has `ε⁽⁰⁾ = 1/Δ + (1−1/Δ)ε`.
- Only an average holds: `E_{s uniform} p_s = ε⁽⁰⁾ + O(Δ/q)`. It is not exact, and it says nothing about a fixed `s`.
- **Counterexample, grid spike.** Set `H = ⌊n/Δ⌋ mod B`, except a special symbol at `Δ|n`. Then `ε ≈ 1/2`, but `p_0` is at chance level.
- **Counterexample, block-constant aligned at 0.** Then `p_0 ≈ 1` while ε≈1/2.

**`E[1/p_s]` vs `1/E p_s`.** Take block-constant H again. Then `p_s ≈ 1 − t/Δ` with `t = s mod Δ`. So `ε̄ ≈ 1/2`, but `E_t[1/p_s] ≈ ln min(Δ,B)`, which is unbounded.
- **Corrected procedure:** build a table, calibrate `p_s` on known scalars (about `1/p_s` samples at `O(log q + c_H)` each), and rebuild if it is low.
- By Markov, `Pr_s[p_s ≥ ε̄/2] ≥ ε̄/2`. So you need at most `2/ε̄` tables in expectation.
- Single-target total: `≲ (2/ε̄)·[M(1+c_H) + calib] + 2(c_H+ν√Δ)/ε̄`.
- This adds a condition the card lacks: `ε̄ ≫ √q/Δ` as well as `ε̄ ≫ √(Δ/q)`. Both equal `q^{-1/6}` at Δ=q^{2/3}. At ε=Θ(1) the extra factor is only a constant.

**Occupancy.** The bound that always holds is `ν_s ≤ M·max_b π_b`. "≈1" needs `max_b π_b ≲ Δ/q`, not just `B ≈ q/Δ`.
- **Counterexample: H ≡ const.** Then ε=1, which passes the card's gate `ε ≫ √(Δ/q)`. But `ν = q/Δ`, so online cost is `q/√Δ ≥ √q`. **The gate as stated is false.**
- Corrected gate, for this decoder only: `M(1+c_H)·R + (c_H + ν_s√Δ)/p_s ≪ √q`, where R is the number of tables built.
- For low-degree interval-bucket H, the Kohel–Shparlinski (KS) bound gives `max π_b ≤ 1/B + O(dL/√q)`. Hence `ν = O(1)` once `Δ ≳ dL√q`.
- KS does **not** control per-bucket anchor counts `N_b`. Those are incomplete progression sums with error about `dL√q log q`, far above the mean of ≈1. The max-π bound is the only rigorous route.

## 2. Fourier statement

**One-sided statistic.** `ε⁽⁰⁾ = Σ_b Σ_a |1̂_b(a)|²·Re D(a)`, where `D(a) = Δ⁻¹Σ_{δ<Δ} e(aδ/q)`.
- Re D behaves like sin(2x)/(2x) with `x = πaΔ/q`, and it dips to about −0.22.
- The baseline is `Σπ_b²`, not `1/B`.
- **Counterexample:** `B=2`, `H = sign cos(2πa₀n/q)` with `a₀ ≈ 0.72q/Δ`. This frequency is inside the card's band |a|≲q/Δ, yet `ε⁽⁰⁾ < Σπ_b²`.
- So "excess = low-band energy" is false. It also contradicts the accepted H019 C1 repair, which uses nonnegative weights and only the band `q/(2L)`.

**Correct nonnegative (Fejér) version.** Draw u, v iid uniform in [0,Δ).
- `ε^F = Pr_{n,u,v}[H(P_{n+u}) = H(P_{n+v})] = Σ_b Σ_a |1̂_b(a)|² K_Δ(a)/Δ ≥ Σπ_b²`.
- `K_Δ/Δ ≥ 4/π²` on `|a| ≤ q/(2Δ)`.
- This statistic is not the success probability of any algorithm here. It is only an upper/lower-bound tool.

**KS closure, restated with corrections:**
- **Averaged over random s:** `|ε⁽⁰⁾ − Σπ²| ≤ O(d²L²B² log q/q)`. The `log q` comes from the `1/|a|` tail of |D|. This closes `B ≪ q^{2/5}(dL)^{-4/5}(log q)^{-2/5}`.
- **Fixed table, any s, deterministic:** every length-Δ window has bucket fraction `π_b ± O(dL√q log q/Δ)`. So `p_s ≤ max π_b + O(dL√q log q/Δ)`, which closes only `Δ ≫ (dL log q)^{2/3} q^{2/3}`.
- **Open for a fixed s:** Δ∈[√q, q^{2/3}·polylog]. This is a gap in the theorems, not evidence of a signal.

**Multi-target claim is wrong.** With `S = M`, the ledger gives `ST² = q·ν²/p² ≥ q` for every Δ. So the condition "`ε ≫ √Δ/q^{1/3}`" is wrong and should be dropped. Any advantage could only come from cheap preprocessing (P ≈ S), which is the single-target claim again.

## 3. Claims not accepted

- **"Exactly two kinds of information":** rejected. The card's own dedup table lists multiplicative-coset structure, which is neither P1 nor P2. Heavy coefficients at high frequency and algebraic relations across several views are also missing. And a ranked/soft posterior search uses guesswork-style cost (expected rank), so the few-bucket hard-match case does not subsume H024.
- **"P2 circular, therefore discarded":** rejected. Width-Δ membership plus doubling is equivalent to width-Δ interval ECDLP, within log factors, and only for worst-case or self-reducible tests. That is a reformulation of the problem, not a closure. Card 1's bucket match is itself an approximate P2 test, so the two classes overlap.
- **Universal standing gate:** rejected. Even repaired, it applies only to fixed-anchor bucketing with window search.
- **Optional <1M probe:** rejected. At q≈3·10⁴ the exact `p_s` costs about `qB` with prefix sums, so sampling "along a progression" is both unnecessary and correlated. The bounds are vacuous at that size (about 36 ≫ 1). There is no H with a rationale, and a single toy size cannot inform scaling.

## 4. Is any numerical test justified now?

**No.** A test becomes admissible only if someone supplies a concrete H with a stated rationale for `p_s/(1+ν_s) ≫ √(Δ/q)` at Δ≥√q. Its preregistration would need:
- exact fixed-table `p_s` and `ν_s`;
- `c_H`, and the cost of any rebuild/calibration;
- at least two sizes, to check scaling.
