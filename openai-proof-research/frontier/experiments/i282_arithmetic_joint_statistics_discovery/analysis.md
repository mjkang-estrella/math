# I282 — Analytic record: a mesoscopic factor vector marked by macroscopic factors

2026-10-12. Discovery only. **No substantial new theorem nominated.** All applicable results at `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. The completed restricted theorem below is technical; the full target remains unpaid. No numerical scan or independent acceptance is claimed.

## 1. Selected exact target

Let `X` tend through real values to infinity, put

\[
 L=\log X,\quad y=\exp(L^{1/3}),\quad N=\pi(2X)-\pi(X),
 \quad A_X(p)=(v_q(p-1):q\le y),
\]

and sample a prime uniformly from `(X,2X]`. Let `V(p)` be the decreasing logarithms of its predecessor's prime factors, with multiplicity, divided by `log(p-1)` and padded by zeros. Let `Q_y` be the law of independent variables `W_q`, one for each prime `q≤y`, with

\[
 \Pr(W_q=0)=1-\frac1{q-1},\qquad
 \Pr(W_q=j)=q^{-j}\quad(j\ge1).
 \tag{Q}
\]

At `q=2` the first probability is zero; positive valuations sum to one. Thus the prime-input local bias is retained.

The single selected full target is: for every fixed integer `k≥1` and every fixed real continuous `H:[0,1]^k→R`, with `μ_H=E_PD(1)H`,

\[
 \sup_{\psi:\,\mathbb N_0^{\{q\le y\}}\to\mathbb R,
                 \ |\psi|\le1}
 \left|\frac1N\sum_{X<p\le2X}H(V_1(p),\ldots,V_k(p))\psi(A_X(p))
                 -\mu_H\,E_{Q_y}\psi\right|\longrightarrow0.
 \tag{M, UNPROVED}
\]

The small-factor test may depend arbitrarily on `X`. Only `H` and `k` are fixed. This is variation convergence of the *small-vector marked measure*, tested weakly in the large coordinates. It is **not** total variation convergence of the entire arithmetic ranked vector to a continuous PD law; that stronger statement would be false by discreteness.

For nonnegative `H` with `μ_H>0`, (M) is equivalent to total variation convergence to `Q_y` of the small vector under sampling biased by `H(V(p))`, together with the stipulated PD marginal. It gives conditional large-factor expectations for moving events of model probability bounded away from zero. It does not give a uniform conditional law on each small-vector atom or on arbitrarily rare events.

This genuinely tests a growing set of valuations. It is not fixed residue conditioning, an Omega congruence, a fixed-bin continuous mapping, or the choice of an unspecified slowly growing diagonal subsequence.

## 2. Paid partial: entire small-vector law under a restricted long-tuple bias

**Proposition P (proved, technical).** Fix `r≥1` and intervals `(a_i,b_i]` with `0<a_i<b_i` and

\[
 \sigma=\sum_{i=1}^r b_i<\frac12.
\]

Let `T_X(n)` count ordered tuples of *numerically distinct* primes `ℓ_i∈(X^{a_i},X^{b_i}]` whose product divides `n`. Put

\[
 C_X^{\varphi}=\sum_{\boldsymbol\ell}\frac1{\varphi(\ell_1\cdots\ell_r)},
 \quad C=\prod_i\log(b_i/a_i)>0.
\]

With `y,A_X,Q_y,N` as above,

\[
 \sup_{|\psi|\le1}
 \left|\frac1N\sum_{X<p\le2X}T_X(p-1)\psi(A_X(p))
                    -C_X^{\varphi}E_{Q_y}\psi\right|\longrightarrow0,
 \qquad C_X^{\varphi}\longrightarrow C.
 \tag{P}
\]

In particular, the whole small vector, under the probability weighting proportional to `T_X(p-1)`, converges in total variation to `Q_y`. The restriction to combined selected mass below `1/2` is essential to the proof budget, not asserted to be necessary for the truth of (M).

### Proof: the summed discrepancy, including the divisor weights

Choose a fixed `θ>0` with `σ+θ<1/2`; then choose fixed `δ>0` so `σ+θ<1/2−δ`. Set `D=(2X)^θ`. Every `y`-smooth integer `d≤D` is coprime to every long prime in the slots for large `X`. Define

\[
 M_T(d)=\sum_{\substack{X<p\le2X\\d\mid p-1}}T_X(p-1),
 \quad M_T=M_T(1),\quad w_y(d)=2^{\omega(d)}+\log y.
\]

Write `ℓ=∏ℓ_i`. Since `(d,ℓ)=1`, the exact count swap gives

\[
 M_T(d)=\sum_{\boldsymbol\ell}
          [\pi(2X;d\ell,1)-\pi(X;d\ell,1)].
 \tag{1}
\]

Define

\[
 E(q)=|\pi(2X;q,1)-\pi(X;q,1)-N/\varphi(q)|.
\]

All moduli in (1) are at most `Q=2^θ X^{σ+θ}≤X^{1/2−δ}` eventually, after decreasing `δ` if needed. A modulus `q=dℓ` determines `d` uniquely: its entire `y`-smooth part is `d`, since each factor of `ℓ` exceeds `y`. It determines the numerical long-prime set uniquely, and there are at most `r!` assignments to the labeled slots. Thus there is no uncontrolled multiplicity in

\[
 \sum_{\substack{d\le D\\P^+(d)\le y}}
 w_y(d)|M_T(d)-NC_X^{\varphi}/\varphi(d)|
 \le r!\sum_{q\le Q}(2^{\omega(q)}+\log y)E(q).
 \tag{2}
\]

The fixed strict exponent margin lets Bombieri–Vinogradov at both endpoints give, for every fixed `B`,

\[
 \sum_{q\le Q}E(q)\ll_B N L^{-B}.
 \tag{3}
\]

Brun–Titchmarsh and PNT give `E(q)≪_δ N/φ(q)` throughout this range. Also

\[
 \sum_{q\le Q}\frac{4^{\omega(q)}}{\varphi(q)}\ll L^4.
 \tag{4}
\]

For completeness, sum over all integers with prime factors at most `Q`, including all powers, to upper-bound the truncated positive sum. Its Euler factors are

\[
 1+4\sum_{j\ge1}\frac1{\varphi(p^j)}
 =1+\frac{4p}{(p-1)^2}=1+\frac4p+O(p^{-2}).
\]

Mertens' prime reciprocal bound proves (4), with the finite small-prime factors harmless. Cauchy with measure `E(q)` now yields

\[
 \sum_{q\le Q}2^{\omega(q)}E(q)
 \le(\sum E(q))^{1/2}(\sum4^{\omega(q)}E(q))^{1/2}
 \ll_B NL^{2-B/2}.
\]

The `log y` part of (2) is at most `L^{1/3}∑E(q)`. Choose `B` after the desired precision. We have proved, for every fixed `A>0`,

\[
 \sum_{\substack{d\le D\\P^+(d)\le y}}
 w_y(d)|M_T(d)-NC_X^{\varphi}/\varphi(d)|\ll_A NL^{-A}.
 \tag{5}
\]

In particular, `M_T=NC_X^φ+O_A(NL^{-A})`. Mertens' theorem on the fixed exponent slots gives `C_X^φ→C`: replace `1/φ(ℓ)` by `1/ℓ` with relative error `O_r(X^{-min a_i})`, and bound each repeated-prime diagonal by `∑_{q>X^{min a_i}}q^{-2}` times bounded harmonic sums. Hence `M_T` is positive and comparable to `N` eventually.

Normalization by `M_T` instead of `NC_X^φ` in (5) remains harmless. Indeed

\[
 \sum_{d\le D}\frac{2^{\omega(d)}+\log y}{\varphi(d)}\ll L^2+L^{4/3}.
 \tag{6}
\]

The same Euler-factor argument with coefficients `2` and `1` proves (6). Increasing the arbitrary precision in (5), we obtain

\[
 \sum_{\substack{d\le D\\P^+(d)\le y}}w_y(d)
 \left|\frac{M_T(d)}{M_T}-\frac1{\varphi(d)}\right|\ll_A L^{-A}.
 \tag{7}
\]

### Proof: the exact Kubilius passage

Take the random integer `B_X=p−1∈[1,2X]` with probabilities proportional to `T_X(p−1)`. Its divisibility probability is `M_T(d)/M_T`. Apply Gorodetsky, **Corollary 2.2**, arXiv:2608.14190v1, PDF p.4 / HTML §2, with ambient bound `2X`, shift parameter `a=−1`, this fixed `θ`, and e.g. `ε=1/2`. The bad-gcd sum is empty because `|a|=1`. Its exact discrepancy weight is `2^ω(d)+log y`, already paid by (7); an unweighted discrepancy cannot simply be substituted. The resulting bound is

\[
 d_{TV}(\mathcal L(A_X\mid T_X),Q_y)
 \ll u^{-\theta u/2}+(2X)^{-\theta/2}+O_A(L^{-A}),
 \qquad u=\frac{\log(2X)}{\log y}\to\infty.
 \tag{8}
\]

Total variation controls every bounded real `ψ` with factor at most two. Multiply (8) by `M_T/N=O(1)` and use its mean estimate to obtain (P). This proof establishes uniformity over all small-vector events, rather than assuming it from a fixed-modulus statement. QED.

**Scope of the partial.** Finite linear combinations of these rectangle tuple statistics satisfy the same conclusion. By uniform approximation on compact supports and the deterministic bound on tuple counts, it extends to continuous compactly supported factorial tests with coordinate sum less than `1/2`. Repeated long-prime occurrences can replace numerical distinctness with `o(1)` error: the exceptional predecessor set has prime-normalized size `O((X^{1-a}+sqrt X)/N)=o(1)` for any fixed lower factor exponent `a>0`, and the tested tuple counts are bounded. Normalizing long-factor logs by `log(p−1)` instead of `log X` uses fixed boundary strips and the already proved `ψ=1` intensities; bounded `ψ` cannot enlarge those absolute errors. These passages do not extend the total-mass support.

This is a rigorous small/large factor partial. Its mechanism is the classical level budget plus an existing general theorem; it is not nominated as a substantial new finding or claimed new to literature.

## 3. Exact sufficient unpaid bridge for the full target

For a fixed nonnegative continuous `H` with `μ_H>0`, let

\[
 N_H=\sum_{X<p\le2X}H(V_1(p),\ldots,V_k(p)),\quad
 M_H(d)=\sum_{\substack{X<p\le2X\\d\mid p-1}}H(V_1(p),\ldots,V_k(p)).
\]

The stipulated D dyadic PD theorem gives `N_H/N→μ_H`. A concrete sufficient additional estimate is: for some fixed `θ_H∈(0,1)`,

\[
 \mathcal R_H(X):=
 \frac1{N_H}\sum_{\substack{d\le(2X)^{\theta_H}\\P^+(d)\le y}}
 (2^{\omega(d)}+\log y)
       |M_H(d)-N_H/\varphi(d)|\longrightarrow0.
 \tag{B, UNPAID}
\]

No claim of (B) is made for arbitrary `H`. Conditional on (B), applying exactly the same Corollary 2.2 to the `H`-biased integer gives

\[
 d_{TV}(\mathcal L(A_X\mid H),Q_y)
 \ll_H u^{-\theta_Hu/2}+(2X)^{-\theta_H/2}+\mathcal R_H(X).
 \tag{9}
\]

The target discrepancy is therefore at most

\[
 2(N_H/N)\,d_{TV}(\mathcal L(A_X\mid H),Q_y)
                   +|N_H/N-\mu_H|.
 \tag{10}
\]

If a nonnegative `H` has `μ_H=0`, domination by its vanishing ordinary mean proves (M) directly. Every real `H` is a difference of two nonnegative continuous functions, for instance `H+c` and `c` with `c>||H||∞`; apply (10) separately. Thus (B) for the indicated nonnegative tests would prove all of (M). This is a **complete conditional reduction**, not a solution of (B).

**Where the paid proof stops.** For the tuple statistic of §2, (B) is proved when `σ+θ<1/2`. D's interior law reaches every fixed compact simplex with selected mass below `1`, but does not state (5) or (B) with a growing smooth-divisor condition. Replacing `σ<1/2` by `σ<1` in (2) preserves the exact count swap; it moves the moduli outside the available classical distribution range. No such change is made here.

The missing estimate is not the existence of the PD marginal, the small-vector marginal, or pointwise convergence for each fixed divisor. It is an **absolute sum of large-factor-weighted discrepancies**, with the displayed divisor weights, for genuinely growing smooth moduli. The conditional reduction identifies a sufficient analytic family rather than claiming its necessity for every possible proof of (M).

## 4. Why the inspected stronger pinned operations do not pay (B)

D `sections/03-determinant.tex`, `thm:type-II`, requires `F(qh)=F(h)` at each selected inert prime. For the target cutoff `exp(L^(1/3))`, every inert prime in its `.1<a_i<.2` bands is below `y`. An arbitrary valuation event is not invariant: `ψ(A_y(qh))` can change when `q` is inserted. For example `ψ=1_{v_q(h)=0}` changes from one to zero at `h=1`. This falsifies direct use of that theorem with the new factor, not the target (M).

D `sections/06-correlations.tex`, `thm:two-sided`, has the **specified** first core `W(n)(T(n)−C_X)` and an invariant second core `G(n_*)`. Allowance of an arbitrary norm-controlled physical vector in `prop:graph-transfer` only bounds the residual pairing with its comparisons. The separate comparison estimates still need their hypotheses. In particular `cor:low-main-term` follows from an unweighted smooth progression sum for `w=ℓd'v`; `ψ(A_y(ℓd'v))` depends on `d'` and `v`. `cor:constant-high` uses the unweighted log-phase estimate, not an arbitrary small-factor weight. No weighted substitute, nor an exactly recombined error surviving extraction, is proved here.

Moving `y` below all mark bands (e.g. to `exp(L^.08)`) removes the literal multiplier counterexample. It does **not** by itself prove the changed endpoint Fourier estimate, weighted presieve mean, or summed prime discrepancy. This narrower variant was screened but not nominated. Conversely moving active small groups above `y` does not move D's inert bands out of `.1,.2`.

D's extraction ends in `C e^(−h)/γ+C sqrt(C_K/b)` after taking the real `X` limit with every depth and number of arrays fixed. A growing-divisor sum with factor `2^ω(d)` does not follow by multiplying this qualitative limit by its number of terms. R006's fixed-progressions law has the same quantifier issue; R008 and R010 pay particular arithmetic modes, not arbitrary small-factor events.

For J, `prop:mixed` and `eq:distribution-characters` have fixed `J` and fixed phase vectors. Finite Fourier inversion explicitly factors the two whole bin-count vectors. Approximating ranked factors on a fixed grid therefore already gives complete joint PD for `(n,n+1)`, as completed I07 §9 records. This deduction uses the stronger actual source, not a false inference from independent largest factors. It is spent.

J's `lem:labels-short`, interpolation formula, and `prop:conclusion-main-vanishes` take `X→∞` before `B→∞`; all residue periods and the finite interpolation coefficients are fixed in that inner limit. Appending a valuation vector with primes up to `y(X)` supplies a growing period and a growing family of tests. The arbitrary testing signs in its sampling proposition concern its prescribed auxiliary site law at fixed `B`; they do not prove this new arithmetic joint law. No rate or growing-grid uniformity was found in the inspected statements. This is a scoped interface limitation, not a theorem that the complete corpus cannot imply (M).

## 5. Complete countermodel to the marginal/fixed-label shortcut

This model diagnoses a logical inference, not a counterexample made from integers. It is stronger than merely observing that two marginals need not be independent.

Let `W=(W_q:q≤y)` have exactly `Q_y`. Put `z=exp(L^(1/6))` and

\[
 C_X(W)=(-1)^{\sum_{z<q\le y}1_{W_q>0}},\quad m_X=E C_X.
\]

Independence gives `m_X=∏_{z<q≤y}(1−2/(q−1))→0`, because the tail prime reciprocal sum is `(1/6)log L+O(1)→∞`. Fix the PD law `μ`. Let `a=E_μ V_1` and `h(V)=V_1−a`. Then `E_μh=0`, `|h|≤1`, and `E_μh²>0` (the PD largest part is nondegenerate). Given `W`, assign the macroscopic partition the probability law with density

\[
 \frac{d\mu_W}{d\mu}(V)=1+\frac12(C_X(W)-m_X)h(V).
 \tag{11}
\]

This is nonnegative since `|C_X−m_X|≤2`, and it integrates to one. Averaging over `W` gives exactly `μ`. Every fixed finite set of valuation coordinates lies below `z` eventually and is independent of `C_X`. After averaging over the tail in (11), those fixed coordinates are **exactly independent** of `V`. The entire small-vector marginal is also exactly `Q_y`.

Nevertheless

\[
 E[(V_1-a)C_X(W)]
       =\frac12(1-m_X^2)E_\mu h^2
       \longrightarrow\frac12 E_\mu h^2>0.
 \tag{12}
\]

Thus (M) fails for the fixed continuous test `H(V)=V_1` and bounded moving test `ψ=C_X`, despite both exact marginals and every fixed local independence statement. Additional abstract fixed labels can be sampled independently without changing (12); this is not claimed to reproduce actual arithmetic identities for Omega.

Even vanishing logarithmic mass is compatible with this obstruction. For (Q), `E W_q=q/(q−1)^2`, so

\[
 E\Big[\frac{\sum_{q\le y}W_q\log q}{\log X}\Big]
       =O(\log y/\log X)=O(L^{-2/3})\to0.
\]

A negligible mass can still carry an order-one correlation in its valuation pattern. Deleting it from a ranked partition cannot establish independence of that pattern.

Finally, for a moving event `E_X`, (M) gives an absolute marked error `ε_X→0`. Dividing to form conditional expectations incurs `ε_X/Q_y(E_X)` and the marginal probability error. Without a lower probability bound or a relative error estimate this proves no uniform rare-event theorem. This is the paid/unpaid boundary for shrinking smoothness thresholds as well.

## 6. Decision

P, (9)–(10), and (11)–(12) are complete rigorous technical work. (M) and (B) are unproved and not refuted arithmetically. The strongest contribution collision is the existing arbitrary-sequence Kubilius theorem of Gorodetsky coupled with the classical restricted large-factor distribution mechanism made explicit by Bharadwaj–Rodgers. The fixed joint PD fallback is additionally already in J and I07. No search absence is used as a novelty argument. No finding is proposed for the user's count; the parent retains the independent proof and significance gates.
