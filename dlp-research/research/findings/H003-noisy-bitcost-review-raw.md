# H003 raw numerical and cost review

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h003-noisy-bitcost-review-fable-20261008-r1`
Provider/model: Factory Claude Fable 5.1. Raw output, NOT adopted wholesale.
Unmeasured group-operation prices and statistical heuristics are qualified in disposition.

# H003 numerical / bit-cost review (read-only; no edits, no children, no experiments)

## Verdict: REPAIR (construction valid; precision resolvable; cost statement needs explicit constants). Main ECDLP gain: NONE.

Finite precision does **not** break polynomiality. The explicit certified bound below is cheap: about 40 significant bits plus exact 2H-bit integer argument reductions, dominated by point formation. The real obstruction is the sample count: the proposal's own parameters give about $2^{112.9}$ predictor calls at $q\approx2^{256}$ even for $\varepsilon=1/4$. Everything after this line is detail supporting that.

## 1. Math inspected (for the companion review; nothing assumed wrong)

I rederived rather than trusted:

- $\hat g(a)=2/[q(1+e^{-2\pi i a/q})]$ for $g(x)=(-1)^x$ on canonical reps, $q$ odd: correct (geometric sum, $(-1)^q=-1$). $|\hat g(a)|=1/(q|\cos(\pi a/q)|)$, mass concentrated near $a\approx q/2$.
- $\|\hat g\|_1 \le 1/q + 2\sum_{j\ge0} 1/(2j+1) \le \ln q + 2.1$. So **$L=4H+4$ is valid but ~5.7× loose at 256 bits** ($1028$ vs $\ln q+3\approx180$). Since cost scales as $L^6$, that is a $2^{15}$ constant. Repair item.
- Triangle step: $|\mathbb E fg| \le L\max_{a\ne0}|\hat f(a)| + 1/q$, so $|\mathbb E fg|\ge2\varepsilon$, $\varepsilon\ge1/q$ gives a nonzero $|\hat f_0(a)|\ge\varepsilon/L=\eta$. **Uses only absolute correlation. Objection 3 confirmed: no sign/orientation is needed.** The old "orientation required" gate should be narrowed to "full-domain magnitude required".
- $\hat f_1(b)=\hat f_0(b/k)$: correct; the heavy $a$ and $ak$ have identical amplitude, so both survive both lists.
- Estimator identity $\mathbb E Z_I = E_I$ with $Z_I=\mathrm{Re}(f(x)f(x-y)D_I(-y)/(qp(y)))$: correct (expand $|\hat f(a)|^2$, substitute $y=x-x'$). Since $f$ is real, $\mathrm{Re}\,D_I(-y)=\mathrm{Re}\,D_I(|y|_q)$, which is even in $y$; this simplifies implementation.
- Bins: for every odd $q$ with $2^{H-1}<q<2^H$, the count $\{0\}$ plus shells $j=0,\dots,H-2$ is exactly $H$; the last shell $[2^{H-2},(q-1)/2]$ is truncated with size $\le 2^{H-1}$. Shell size $\le 2|y|_q$ holds everywhere, so $|Z_I|\le H$ holds, including $y=0$ ($|I|H/q\le H$).
- Dirichlet bound $|D_I(y)|\le 1/|\sin(\pi y/q)|\le q/(2|y|_q)$: correct (Jordan).
- Hoeffding: range $2H$, $t=\eta^2/8$ gives $m\ge128H^2\eta^{-4}\ln(2N/\delta_s)$; the proposal's $\ln(4N/\delta_s)$ is conservative. Adaptive union bound with fresh samples per test is valid (each test's failure is conditionally independent of history; sum over at most $N$ performed tests). The deterministic caps (≤$4/\eta^2$ retained per level, ≤$N$ tests, abort otherwise) make work bounded regardless of statistical failure. Parseval count uses $\|f\|_2^2\le1$ and disjointness of same-level intervals: fine.
- Threshold logic ($\ge\eta^2/2$ retain, total error $\le\eta^2/4$): amplitudes $\ge\eta$ survive; retained have true energy $\ge\eta^2/4$; leaf list $\le4/\eta^2$; pairs $\le16/\eta^4$. Fine.

No sign/normalization error found.

## 2. Certified precision: explicit algorithm and bound (answers the main question)

Write $I=[A,A+n-1]$, $M=2A+n-1$. Closed form: $\mathrm{Re}\,D_I(y)=\cos(\pi M y/q)\cdot\sin(\pi n y/q)/\sin(\pi y/q)$.

**Key observation:** the required accuracy is relative to the *a priori* bound $q/(2|y|_q)$, never to the actual (possibly tiny) value. Required absolute error on $\mathrm{Re}\,D_I$ is $\tau(y)=\eta^2 q/(16H|y|_q)$, because the weight is $w(y)=H\cdot\mathrm{size}/q\le 2H|y|_q/q$. So numerator cancellation is harmless, and the near-zero denominator only needs *relative* accuracy.

Per sample, $y\ne0$:

1. $y'=|y|_q\in[1,(q-1)/2]$ (exact).
2. $u=My' \bmod 2q$, $v=ny'\bmod 2q$: exact bignum, two $H$-bit mult-mods (≈ one field multiplication each).
3. $\tilde c\approx\cos(\pi u/q)$, $\tilde S\approx\sin(\pi v/q)$ with **absolute** error $\le2^{-P}$; $\tilde s\approx\sin(\pi y'/q)$ with **relative** error $\le2^{-P}$ (argument in $(0,\pi/2]$, so relative accuracy of the argument transfers; the argument $y'/q$ is formed as an exact integer quotient $\lfloor y'2^{H+P+8}/q\rfloor$).
4. $\tilde R=\mathrm{fl}(\tilde c\tilde S/\tilde s)$, relative rounding $\le2^{-P}$ per op.
5. $\tilde Z=\mathrm{round}_{2^{-P}}\big(f(x)f(x-y)\cdot\tilde R\cdot H\cdot\mathrm{size}(\mathrm{bin}(y))/q\big)$; clamp to $[-H,H]$; store integer $\hat z=\tilde Z 2^P$.

Error: $|\tilde R-R|\le 7\cdot2^{-P}\cdot q/(2y')$, times $w(y)\le2Hy'/q$ gives $\le7H2^{-P}$, plus final rounding $2^{-P}$. Requiring $8H2^{-P}\le\eta^2/16$:

$$P=\left\lceil\log_2\frac{128H}{\eta^2}\right\rceil=\left\lceil 7+\log_2H+2\log_2L+2\log_2(1/\varepsilon)\right\rceil .$$

For $y=0$: $D_I(0)=|I|$ exactly; $Z=f(x)^2|I|H/q$ is an exact rational. No numerics at all.

Accumulation: sum the $\hat z$ as exact integers (≤ $P+\log_2(m(H+1))$ bits); compare $\sum\hat z\ \ge\ m\cdot2^P\cdot\eta^2/2$ exactly with $\eta^2=\varepsilon^2/L^2$ rational. Total numerical error $\le\eta^2/16<\eta^2/8$ budget. No cancellation issue in the mean.

Concrete: $H=256$, $L=1028$, $\varepsilon=1/4$: $P=40$. **IEEE double with a correctly rounded libm (CORE-MATH/CRlibm) or ball arithmetic (Arb) suffices** down to $\varepsilon\approx2^{-5}$; double-double or 128-bit MPFR to $\varepsilon\approx2^{-32}$. Working mantissa $P+16$ with exponent range $\ge H+16$, or fixed-point at $H+P+16\approx312$ bits if one wants the dumbest certifiable option. Per sample: 2 bignum mult-mods + 1 bignum division + 3 trig + 3 flops. In group-add units $C_{est}\approx2^{-3}$ to $2^{-2}$ (a 256-bit EC add is ≈12 field mults; the bignum work here is ≈2–3 field mults).

So: **yes, finite precision stays $\mathrm{poly}(\log q,\log1/\varepsilon,\log1/\delta)$, with the explicit bound $P$ above, and is negligible against point formation (≈$H/8$ to $H$ group adds per call).** Precision is not the gap.

Other implementation items, all closed:
- Exact sampling: rejection sampling for $x\in\mathbb Z_q$ ($H$ bits, expected <2 tries), bin index ($\lceil\log_2H\rceil$ bits), $y$ in shell $j$ ($j+1$ bits exactly; last shell by rejection). Expected $\le 4H+2\log_2 H$ random bits per sample; total exceeds $5H\times$samples only with probability $e^{-\Omega(\text{samples})}$, or cap and charge to $\delta$.
- Union/confidence: $\delta/2+\delta/2$, plus optional sampling-cap abort. Output is verified, so failures are "no answer", never wrong. Optimal choice is $\delta=1/2$ and restart with fresh coins (predictor is a fixed function, so restarts are independent): expected factor 2.
- Lists: $\le4/\eta^2$ inversions (reuse per $a$), $\le16/\eta^4$ mult-mods and scalar mults for verification. Memory for both lists: $8L^2\varepsilon^{-2}H$ bits = 4 GiB at $L=1028,\varepsilon=1/4$; 128 MiB with $L'$. Per-level interval working set is the same order. Rho needs none of this.

## 3. Hypothetical symbolic cost at $q\approx2^{256}$ (query counts, not a benchmark)

Pair count $N\cdot m\approx1024H^3\eta^{-6}\ln(64H\eta^{-2}/\delta)$; predictor calls $=4Nm$; point formations $=4Nm$. Per call cost $C_{point}+C_B$: fixed-base comb $\approx2^5$ adds (naive table $\approx2^7$); $C_B$ unknown, A1-style (5 shifted points + 5 character/phi evals with inversions) plausibly $2^3$–$2^8$. I use $C_{point}+C_B=2^{6.6}$ (32+64). Rho with negation: $0.886\cdot2^{128}=2^{127.8}$. $\delta=1/2$ (add 1 bit for expected restarts).

| $\varepsilon$ | calls, $L=4H+4$ | $W$, $L=4H+4$ | calls, $L'=\ln q+3$ | $W$, $L'$ |
|---|---|---|---|---|
| $2^{-2}$ | $2^{112.8}$ | $2^{119.4}$ | $2^{97.5}$ | $2^{104.1}$ |
| $2^{-3}$ | $2^{118.9}$ | $2^{125.5}$ | $2^{103.6}$ | $2^{110.2}$ |
| $2^{-4}$ | $2^{124.9}$ | $2^{131.5}$ | $2^{109.7}$ | $2^{116.3}$ |
| $2^{-6}$ | $2^{137.1}$ | $2^{143.7}$ | $2^{121.8}$ | $2^{128.4}$ |

Verification ($16\eta^{-4}C_{point}\approx2^{57}\varepsilon^{-4}$) and setup are negligible. Information-theoretic floor at $\varepsilon=1/4$ is ≈$1.4\times10^3$ queries; the construction is $2^{87}$–$2^{102}$ above it, so "not optimal" is an understatement. The leading constant is $2^{24}H^9\ln(\cdot)$ as proposed, $\approx2^{9}H^9\ln(\cdot)$ with $L'$.

**Concrete 256-bit break-even for this construction: $|\text{full-domain correlation}|=2\varepsilon\gtrsim 2^{-2.5}$ as written, $\gtrsim2^{-5}$ with $L'$.** The asymptotic $\beta<1/12$ statement is true but says nothing at 256 bits unless $\varepsilon$ is essentially constant.

Optional further repair (KM-style): reuse one $m'$-sample batch per level for all intervals at that level, union-bounding over all $\le2q$ tree intervals ($m'=128H^2\eta^{-4}\ln(4q/\delta_s)$, ≈7× larger than $m$ at 256 bits). This cuts predictor calls and point formations from $4Nm$ to $4Hm'$ (≈$2^{20}\varepsilon^{-2}$ fewer) but the (interval, sample) pair count is invariant at ≈$7Nm$, each costing $C_{est}$. Net gain is bounded by $(C_{point}+C_B)/C_{est}\approx2^{9}$, moving break-even to about $\varepsilon\approx2^{-6.5}$ with $L'$. Exponent stays $\varepsilon^{-6}$; the per-unit cost shifts from point/predicate to bignum argument reduction. Requires storing nothing extra beyond the per-level interval list.

## 4. Full-work gate (expected, single target)

$$
W(\varepsilon)=\frac{4Nm\,(C_{point}+C_B)+2Nm\,C_{est}+16\eta^{-4}(C_{point}+C_{mulmod})+4\eta^{-2}C_{inv}+W_{setup}}{1-\delta}\ <\ \sqrt{\pi q/4},
$$
$N=\lceil8H/\eta^2\rceil+2$, $m=\lceil128H^2\eta^{-4}\ln(8N/\delta)\rceil$, $\eta=\varepsilon/L$, $P$ as in §2 (prescribes the arithmetic). If list$_0$ is amortized over many targets with fixed $(E,G)$, halve $Nm$ and compare against Bernstein–Lange with matched advice $4L^2\varepsilon^{-2}H$ bits and matched precomputation $2Nm$ calls; the $f_0$ search is the calibration and is never free.

## 5. Remaining assumptions (all conditional, none discharged)

1. A fixed, stateless $B_G:E(\mathbb F_p)\to[-1,1]$ exists with $|q^{-1}\sum_{r\in\mathbb Z_q}B_G([r]G)(-1)^r|\ge2\varepsilon$ over the **full** domain (exclusions count as 0), at the target $(E,G)$, for the canonical-rep parity. Arbitrary fixed errors OK; randomized $B$ needs fresh independent coins per call; stateful/query-detecting $B$ breaks it.
2. $\varepsilon$ must be known to within a factor 2 (halving search costs $\le1.02\times$ the final-$\varepsilon$ cost, since verification certifies success).
3. $B_G$ outputs are dyadic with $\le P$ bits (else add 1 bit to $P$).
4. Certified arithmetic: correctly rounded or ball-arithmetic trig; exact bignum reductions mod $2q$; exact integer accumulation; rejection sampling from a true uniform bit source.
5. Cost model: group-add units; $C_B$ is unmeasured and dominates uncertainty by up to $2^5$.
6. The $\ell_1$ bound $L'=\ln q+3$ needs the companion's sign-off before replacing $L=4H+4$ in any accepted gate.
7. Not claimed: optimality of $\varepsilon^{-6}$, novelty over AGS/KM (the exponent equals Kushilevitz–Mansour's; Levin-style refinements exist for $\mathbb Z_2^n$ and are not derived here), or any finite-size speedup. The $\varepsilon^{-11}$ route is superseded as the explicit sufficient bound, not refuted.

## 6. Should a larger A1 pilot be funded?

Not as a scaling or learning investment. The gate demands $|\text{corr}|\ge2^{-5}$ to $2^{-2.5}$ at 256 bits, non-decaying in $q$. The A1 data are consistent with pure noise: at $q=139$ the null standard deviation is $1/\sqrt{138}\approx0.085$; the largest observed $|N|/n$ (30/138 = 0.22, partial) is 2.55σ, which is the expected maximum of 41 near-independent comparisons. Signs flip across cases, and the five-offset/c=−1 observation is a post-hoc selection.

A pilot is justifiable only as a cheap pre-registered **kill test**: a data-independent family fixed in advance, sign-free full-domain statistic with identity windows as 0, exact enumeration over all $r\in\mathbb Z_q$ at three or more sizes $q\le2^{24}$ (no sampling error; ≈$10^7$ predictor evaluations total), pass threshold $|\text{corr}|\ge2^{-4}$ at every size. Failure rejects the A1 predicate route for this reduction. Nothing in the current data raises the prior of passing above noise, so fund it only if its total cost is negligible relative to other open work.

Summary for root integration: accept the reduction as a valid conditional sufficient construction with the explicit precision prescription of §2 (closes objection 2); confirm objection 3 (absolute correlation suffices); replace the bare "$\varepsilon^{-6}$, $\beta<1/12$" claim with the §3 table and §4 gate; adopt $L'$ pending companion check; no recovery implementation or scaled A1 run beyond the kill test above.
