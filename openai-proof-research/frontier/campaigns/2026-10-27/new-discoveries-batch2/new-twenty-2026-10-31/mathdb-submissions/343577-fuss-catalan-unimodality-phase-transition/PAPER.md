# A logarithmic-derivative proof of the Fuss–Catalan unimodality threshold

Lean proves the complete unimodality phase-transition classification for the measure on the real line defined by the explicit density in Proposition 1.1, formula (2), of Młotkowski–Sakuma–Ueda, *Free Self-decomposability and Unimodality of the Fuss–Catalan Distributions*, arXiv:1908.07887, *J. Stat. Phys.* **178** (2020), 1055–1075. The identification of this density-defined measure with the moment-defined law μ(p,r), **including its normalization to total mass one**, is the source's Proposition 1.1 (and its consequence (3)), cited here; neither that identification nor normalization is proved in Lean. Thus the mathematical resolution of the source conjecture combines the kernel-checked density-measure classification with a cited published theorem. It is not a kernel-checked formalization of the moment-defined statement.

## Statement and source definitions

The MathDB 343577 record reads verbatim:

> Let $p>1$ and let $\mu(p,r)$ denote the Fuss–Catalan distribution with parameters $p$ and $r$. **Phase-transition conjecture.** For every $p>1$ there exists $r_{0}(p)$ satisfying
>
> $$p-1<r_{0}(p)<p,$$
>
> such that $\mu(p,r)$ is unimodal if and only if either $r=p$ or $0<r\leqslant r_{0}(p)$. This conjecture is suggested by the results in the preceding sections and by numerical experiments; the general phase transition remains open.

The parameter domain inherited from the source is p≥1, 0<r≤p; throughout this manuscript p>1. The source Introduction defines the Raney numbers by

\[
 A_k(p,r)=\frac r{k!}\prod_{i=1}^{k-1}(kp+r-i)
 =\frac r{kp+r}\binom{kp+r}{k},\qquad A_0(p,r)=1,
\]

and defines μ(p,r) as the probability law with these moments:

\[
 A_k(p,r)=\int_{\mathbb R}x^k\,\mu(p,r)(\mathrm dx).
\]

The source also says that the measure is absolutely continuous except for μ(1,1)=δ₁. That exception is outside our domain. In particular there is **no atom when r=p>1**.

For p>1 put a=p−1, T=π/p, and X=pᵖ(p−1)¹⁻ᵖ. Proposition 1.1 defines exactly

\[
 \rho(t)=\frac{\sin(pt)^p}{\sin t\,\sin((p-1)t)^{p-1}},\qquad 0<t<T,                 \tag{1}
\]

and states that it decreases bijectively from (0,T) onto (0,X). Formula (2) is

\[
 W_{p,r}(\rho(t))=
 g_r(t):=\frac{\sin((p-1)t)^{p-r-1}\sin t\sin(rt)}
 {\pi\sin(pt)^{p-r}},\qquad 0<t<T.                                         \tag{2}
\]

All powers here are real powers of positive numbers. The Lean functions `rho`, `angularDensity`, `supportRight`, and `density` reproduce (1)–(2). Specifically `density p r x` is g_r(ρ⁻¹(x)) on (0,X) and zero elsewhere; `mu p r` is Lebesgue measure with that density, through `ENNReal.ofReal`. Assigning zero at the support endpoints changes no measure.

The source §2.2.1 gives the following definition (mathematical notation transcribed):

A measure is unimodal when it admits a nonnegative density increasing to a mode and decreasing after that mode, together with an optional nonnegative atom at the mode. The two monotonicity intervals exclude the mode itself.

The corresponding Lean definition is:

```lean
def Unimodal (ν : Measure ℝ) : Prop :=
  ∃ (b c : ℝ) (f : ℝ → ℝ), 0 ≤ c ∧ (∀ x, 0 ≤ f x) ∧ Measurable f ∧
    MonotoneOn f (Iio b) ∧ AntitoneOn f (Ioi b) ∧
      ν = ENNReal.ofReal c • Measure.dirac b +
        volume.withDensity (fun x => ENNReal.ofReal (f x))
```

The monotonicity intervals exclude the mode. Thus a density with an infinite one-sided limit at zero is permitted: its value at the single point zero can be assigned any finite value. No bounded-density condition is imposed. The decomposition permits arbitrary a.e. representatives and an atom; the Lean necessity proof handles both.

## What the Lean statement covers

The principal proved theorem is `FussCatalan.density_measure_phase_transition`:

```lean
∀ p : ℝ, 1 < p → ∃ r0 : ℝ, p-1 < r0 ∧ r0 < p ∧
  ∀ r : ℝ, 0 < r → r ≤ p →
    (Unimodal (mu p r) ↔ r = p ∨ r ≤ r0)
```

This is a theorem about the **actual measure** defined by (1)–(2), not a derivative-based redefinition of unimodality. Coordinate bijectivity, inverse continuity, measurability, nonnegativity, support, nonzero mass, and the equivalence with the source's unimodality predicate for this density measure are proved in Lean. Both directions hold, with the strict threshold bounds, its included endpoint, all real p>1, the full range 0<r≤p, and the r=p case. The printed dependencies are precisely `propext`, `Classical.choice`, `Quot.sound`.

The citation boundary includes the identification with the moment-defined law and its normalization. Proposition 1.1 identifies (1)–(2) as the density of that probability law; formula (3) states the resulting moment identity, whose k=0 case is total mass one. These published facts are cited in the mathematical argument and are not Lean hypotheses, axioms, or kernel-checked conclusions of this packet. Unimodality is unchanged by positive scaling, so normalization is unnecessary for the classification proof itself.

The selected Lean endpoint is `density_measure_phase_transition`, accompanied by `mu_supported` and `mu_ne_zero`. It does not assert `IsProbabilityMeasure (mu p r)` or `IsRaneyLaw p r (mu p r)`. The historical definitions `DensityConjecture` and `LiteralConjecture` remain in the source; no theorem of either type is claimed. In particular `densityConjecture_iff_normalization` records the relation to an earlier, stronger target, rather than an outstanding obligation of the endpoint selected here.

The theorem uses every real p>1 and every 0<r≤p, has strict bounds p−1<r₀<p, includes r=r₀, and treats r=p separately. This is the source conjecture's parameter domain. The source notes after (3) that for r>p>1 its formula W becomes negative on a subinterval. That signed extension is not a probability law in this family and is outside this theorem; applying `ENNReal.ofReal` to it would change the signed object.

## Coordinate and density properties

Every sine in (2) is positive on (0,T), for 0<r≤p. Hence g_r is positive and continuous there. Set h(z)=z cot z. For 0<z<π,

\[
 h'(z)=\frac{\sin z\cos z-z}{\sin^2z}<0,
\]

because sin(2z)<2z. Thus whenever 0<s<u and 0<ut<π,

\[
 u\cot(ut)<s\cot(st).                                                     \tag{3}
\]

The logarithmic derivative of ρ is

\[
 L(t)=p^2\cot(pt)-\cot t-a^2\cot(at)
 =a\{p\cot(pt)-a\cot(at)\}+\{p\cot(pt)-\cot t\}<0.
\]

Its endpoint limits are X at 0 and 0 at T. The former follows by cancelling the common powers of t using sin z=z sinc z and sinc(0)=1; the latter follows immediately from sin(pt)→0 and the positive denominator at T. Continuity, strict decrease and the intermediate value theorem give the claimed bijection. Its inverse is continuous: its strict order reversal and interval image give continuity by the monotone inverse principle. Composing with that inverse proves continuity of W on (0,X). Extending by zero gives a measurable nonnegative density. Its measure is supported in [0,X] and is nonzero, since the continuous density is positive on the nonempty interior interval. These properties are all kernel-checked, without a normalization premise.

## The logarithmic derivative and parameter order

Differentiating the logarithm of (2) gives

\[
 D(r,t)=(p-r-1)a\cot(at)+\cot t+r\cot(rt)-(p-r)p\cot(pt).                    \tag{4}
\]

The code proves this derivative identity for the displayed g_r, not merely for an auxiliary formal expression. Positivity of g_r and the real mean value theorem give

\[
 g_r\text{ nondecreasing on }(0,T)
 \quad\Longleftrightarrow\quad D(r,t)\ge0\ \text{for all }0<t<T.             \tag{5}
\]

Rewrite (4) as

\[
 D(r,t)=a^2\cot(at)+\cot t-p^2\cot(pt)
 +r\{p\cot(pt)-a\cot(at)\}+r\cot(rt).                                    \tag{6}
\]

The coefficient in braces is strictly negative by (3), and r cot(rt) is strictly decreasing as a function of positive r≤p, again by (3). Consequently D is strictly decreasing in r on (0,p]. This finite-difference proof is exactly what Lean uses; it does not require an additional mixed derivative.

Let

\[
 S=\{r:0<r<p,\ D(r,t)\ge0\text{ for all }0<t<T\}.
\]

Equation (6) makes S downward closed among positive parameters. For each fixed t, D(·,t) is continuous inside (0,p), because sin(rt) is nonzero. Therefore every closure point of S lying in (0,p) still belongs to S.

## Why measure unimodality is exactly (5) when r<p

When 0<r<p, the numerator in (2) tends at T to a finite strictly positive number, while sin(pt)^{p−r} tends to zero through positive values. Hence g_r(t)→+∞ as t→T−. Since ρ(t)→0, the density is unbounded in every interval (0,b) with b>0. Lean proves this unboundedness directly by simultaneous eventual inequalities for g_r and ρ.

If the measure is unimodal, its decomposition has no atom, because any Lebesgue-density measure assigns zero to each singleton. Equality of the two density measures therefore gives equality of the density representatives almost everywhere. Write the monotone representative as f and its mode as b.

Suppose b>0. Fix c=b/2. For a.e. x∈(0,min(c,X)), monotonicity on (−∞,b) gives W(x)=f(x)≤f(c). A continuous function on an open interval which obeys a bound almost everywhere obeys it everywhere: otherwise an open neighborhood on which it violates the bound has positive Lebesgue measure. This contradicts the unboundedness near zero. Thus b≤0.

On the positive interior interval the representative f is consequently nonincreasing. Its continuous a.e.-equal density W is nonincreasing too. Here is the precise argument formalized in the packet. If x<y but W(x)<W(y), choose disjoint ordered neighborhoods of x and y where W stays below and above the midpoint of these two values. The a.e.-equality set is dense, so choose u and v in these neighborhoods at which f=W. Then u<v but f(u)<f(v), a contradiction. Thus W is nonincreasing on (0,X).

The decreasing coordinate changes this to g_r nondecreasing. Conversely, if g_r is nondecreasing, W is nonincreasing on (0,X), and the zero extension is nonincreasing on (0,∞) and constant zero on (−∞,0). It supplies the source's decomposition with mode zero and atom coefficient zero. This proves the measure equivalence

\[
 \operatorname{Unimodal}(\mu_{\rm density}(p,r))
 \quad\Longleftrightarrow\quad r\in S\qquad(0<r<p).                         \tag{7}
\]

No probability normalization is used in either direction of this bridge.

## Strict extension above p−1

At r=a=p−1, trigonometric addition gives

\[
 D(a,t)=\cot t+a\cot(at)-p\cot(pt)
 =\frac{\sin^2(at)+a\sin^2t}{\sin t\sin(at)\sin(pt)}>0.                     \tag{8}
\]

Pointwise positivity is not by itself stable uniformly in t. Define F(r,t)=t(T−t)D(r,t) in the interior. The correct joint extension has

\[
 F(r,0)=T,\qquad F(r,T)=T(p-r).                                           \tag{9}
\]

For clarity, the code constructs the extension explicitly, using q(z)=cos z/sinc z with q(0)=1. Near t=0 it equals

\[
 (T-t)\{(p-r-1)q(at)+q(t)+q(rt)-(p-r)q(pt)\}.                              \tag{10}
\]

Near t=T it equals

\[
 t(T-t)\{(p-r-1)a\cot(at)+\cot t+r\cot(rt)\}
 +(p-r)tq(p(T-t)).                                                        \tag{11}
\]

The identity cot(π−z)=−cot z gives (11). At t=0 all q terms in (10) equal one and their coefficients sum to one; at t=T the first term of (11) vanishes and q(0)=1. For r near a, all the other sine denominators at T remain nonzero. These formulas prove joint continuity at the slice r=a, including its two endpoints. Interior continuity follows from the nonvanishing sine factors. This establishes exactly the continuity needed for the compact-slice argument; no interchange of nonuniform limits is used.

By (8)–(9), F(a,t)>0 on [0,T]. Compactness and joint continuity give δ>0 such that F(r,t)>0 for every t∈[0,T] whenever |r−a|≤δ. Choosing 0<ε≤δ with ε<1 gives q=a+ε<p and q∈S. Therefore sup S>a.

## A strict gap below p and the included threshold

At r=p,

\[
 D(p,t)=-a\cot(at)+\cot t+p\cot(pt)\longrightarrow-\infty
 \quad(t\to T^-).
\]

The first two terms have finite limits and the last diverges negatively. Choose an interior t* with D(p,t*)<0. By continuity in r at this fixed t*, there is b<p such that every admissible r is at most b. Thus S is bounded above by a number strictly smaller than p.

Put r₀=sup S. Nonemptiness, the strict lower witness and the strict upper gap give

\[
 p-1<r_0<p.
\]

The supremum belongs to the closure of S and lies inside (0,p), so the relative closedness already proved gives r₀∈S. Downward closure gives every positive r≤r₀, and the supremum property excludes every r>r₀. Hence

\[
 S=(0,r_0].                                                              \tag{12}
\]

This is `derivative_threshold` in Lean. Combining (7) and (12) proves both directions for all r<p, including r=r₀.

## The exceptional case r=p

The angular density simplifies exactly to

\[
 g_p(t)=\frac{\sin t\sin(pt)}{\pi\sin(at)},\qquad
 g_p'(t)=\frac{\sin^2(pt)-p\sin^2t}{\pi\sin^2(at)}.                         \tag{13}
\]

The packet proves the derivative identity directly by the quotient rule, sine addition and sin²+cos²=1. In particular this case has no atom and g_p(t)→0 at T, rather than the blow-up used for r<p. At the other endpoint, (13) and sin(st)∼st give g_p(t)∼pt/(πa)→0. These endpoint values are a.e. irrelevant; only the T-limit is a separate Lean endpoint in this packet.

The positive ratio R(t)=sin(pt)/sin t is strictly decreasing: the derivative of its logarithm is p cot(pt)−cot t<0 by (3). Its endpoint limits are p at zero and 0 at T. Since p>√p>0, the intermediate value theorem gives t₀∈(0,T) with R(t₀)=√p. Strict decrease puts R above √p before t₀ and below afterwards. Equation (13) then shows that g_p is nondecreasing before t₀ and nonincreasing afterwards. Composition with the decreasing bijection ρ gives a single peak at ρ(t₀). Extending the density by zero outside its positive support preserves the two required order properties. The source's measure definition therefore holds, with zero atom. This is `unimodal_at_p`.

The exceptional case and (7)–(12) prove the classification claimed in the principal Lean theorem. On paper, Proposition 1.1 identifies the density measure as the probability law with the prescribed moments, giving the source conjecture. The identification and normalization in this deduction are precisely the published facts on the cited side of the boundary; the moment-defined conclusion is not itself a Lean theorem.

## Prior art and significance

The cross-model Opus review, `t1-prelean-X2-opus-20261120-r1/REVIEW-343577.md`, gives the following prior-art conclusion: “Conclusion: nothing public found (bounded search).” Its citing-paper assessment is reproduced here:

> “Citing papers: OpenAlex refused me (daily budget exhausted), and I respected that. The two Sol lanes independently got the same five citing papers from OpenAlex and Semantic Scholar: 2003.05382, 2107.09473, 2111.10150, 2202.11848, 2206.04932. I re-read the saved list; none is about this threshold. My three web searches (extended and standard) for the phase transition, r₀(p), Raney unimodality, and 2022–2026 work by the authors found only the source, its journal version and unrelated unimodality papers (free Brownian motion, 1710.08240 and 2009.13848).”

The discovery lane also read the journal version, which retains Conjecture 4.10, and screened the named public archives. Its attempted arXiv API query returned 429 and ProbXiv returned 402; neither refusal was bypassed. The final independent review refreshed the arXiv history and keyword API, Semantic Scholar citing list, web searches, local archive screens, and omega issues and pull requests. No matching resolution was found. The current Semantic Scholar list still contains these five papers; the OpenAlex citing-list refresh returned HTTP 429 and was not bypassed. Both omega issue searches and both matching pull-request searches (source id and “Fuss-Catalan unimodality”) were empty. The local archive screen does not assert equality with current remote heads. These are bounded prior-art checks, not a proof of novelty.

The proof is elementary and short once D is viewed as a function of the parameter r. Its substantive step is that this logarithmic derivative strictly decreases with r; the compact endpoint extension supplies the required strict lower margin. Published special-slice results do not themselves give either fact or the threshold classification. The Opus review regards routine status as the weakest point and leaves that campaign-level judgment to root. This packet establishes no new general theory of free probability and claims no kernel proof of the contour-integral moment formula. Its concrete contribution is a kernel-checked continuum-parameter unimodality classification for the exact published density measure, with identification and normalization supplied by a cited published theorem.

## Reproducibility

Lean 4.34.1 and the pinned Mathlib revision are recorded in PINS.json. Only specific imports are used. Every final module is compiled and independently kernel-checked by the copied 32 GiB runner; it limits Lean to one thread and the runner to two affinity CPUs, within the eight-core bound. The appendix contains every source module byte-for-byte in dependency order. REPORT.md records the proved endpoint, the earlier normalization target, allowed dependencies, source hashes and per-module receipts. The present paper uses the citation boundary stated above. The final review does not rebuild the packet; the root independently checks compilation and kernel receipts. No git command, external write, submission, publication or message to another person was used.

## References

1. W. Młotkowski, N. Sakuma and Y. Ueda, *Free Self-decomposability and Unimodality of the Fuss–Catalan Distributions*, arXiv:1908.07887; *J. Stat. Phys.* **178** (2020), 1055–1075, DOI 10.1007/s10955-020-02488-1.
2. P. J. Forrester and D.-Z. Liu, *Raney distributions and random matrix theory*, *J. Stat. Phys.* **158** (2015), 1051–1082, Proposition 2.1 (the density theorem quoted as Proposition 1.1 of reference 1).
