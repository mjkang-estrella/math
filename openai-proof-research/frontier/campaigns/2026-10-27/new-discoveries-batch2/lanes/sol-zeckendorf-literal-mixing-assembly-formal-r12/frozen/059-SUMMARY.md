# Uniform asymptotic probability estimates

Solo implementation, 2026-10-30. Counts remain 9 additional /39 total /next40. Root alone accepts. Full-source, novelty and final mixing remain HOLD.

All fifteen inherited mathematical modules, Literal through SuffixUnion, are byte-identical to the frozen r10 input. New modules: Growth, Uniform, UniformSuffix. No manuscript, shared, git, browser, public, or MathDB changes. No children or external retrieval.

Exact interfaces in namespace LiteralGame:

* `intervalError n = Real.exp (-(n:ℝ)) + (4/(n:ℝ)^18 + 6/(n:ℝ)^3 + 4/(n:ℝ)^9)`.
* `intervalError_limit : Tendsto intervalError atTop (𝓝 0)`.
* `actual_interval_uniform : ∀ᶠ n : ℕ in atTop, ∀ N : ℕ, F n ≤ N → N < F (n+1) → ∀ a : ℤ, (∑ w ∈ completeDomain N, (P N w:ℝ) * (if a ≤ (w.length:ℤ) ∧ (w.length:ℤ) ≤ a+(3*n^6:ℕ) then 1 else 0)) ≤ intervalError n`.
* `suffixError n = Real.exp (-(n:ℝ))`.
* `actualSuffixMass N n = ∑ w ∈ completeDomain N, (P N w:ℝ) * (if n^6 < w.length-lastSplit w then 1 else 0)`.
* `suffixError_limit : Tendsto suffixError atTop (𝓝 0)`.
* `actual_suffix_uniform : ∀ᶠ n : ℕ in atTop, ∀ N : ℕ, F n ≤ N → N < F (n+1) → actualSuffixMass N n ≤ suffixError n`.

These bounds quantify over EVERY N in the Fibonacci interval, and the interval estimate over EVERY integer a. There is no N subsequence, conditional growth premise, or assumed exponential domination. F n is literally Nat.fib(n+1). T is literally w.length; lastSplit is inherited unchanged.

The polynomial mark threshold is exactly M=n^20. The explicit vanishing interval error differs from the suggested exp(-n)+30/n^3: keeping the three inverse-power terms avoids an unnecessary extra comparison. The denominator estimates hold for n≥2. The eventual interval proof also takes n≥12; the suffix proof holds for n≥32. Small n and N=0 are outside the eventual assertion and cause no positivity assumptions or division-by-zero bridges.

Residuals: no mathematical residual for these two endpoints. No log-index n(N), source sigma-algebras, observability, alpha/mixing, final source assembly, prior-art clearance, novelty or acceptance claim. A later assembly can choose the Fibonacci interval.

Audit, fresh source-only replay, resource records and final integrity status are in audit.json, replay-receipt.json, implementation-receipt.json and verification-receipt.json. Failures and attempted sources are retained separately.
