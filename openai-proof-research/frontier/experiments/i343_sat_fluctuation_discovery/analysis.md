# I343: higher deletion moments and the remaining Gaussian gap

Date: 2026-10-13. Status: **substantial target unresolved; paid partial results below**.

## 1. Exact law, notation, and source dependencies

Fix an integer k ≥ 3. For n ≥ k, let C₁,C₂,… be independent uniform proper signed k-clauses: each clause uses k distinct variables chosen uniformly, and independent fair signs. Whole clauses may repeat. Define F₀ = true, Fₘ = ∧_{j≤m} Cⱼ, and

\[
H_n=\min\{m\ge1:F_m\text{ is unsatisfiable}\}.
\]

For a fixed real B > 0, put L = ⌊Bn⌋ and T = min(Hₙ,L). Omit Cᵢ without renumbering the other indices, let T⁽ⁱ⁾ be the capped first unsatisfiable index of that process, and let Dᵢ = T⁽ⁱ⁾ − T ≥ 0. The case L = 0 has no coordinates and T = 0.

All upstream assertions used here are stipulated true at OpenAI/math revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. The actual sources read are authenticated in input-authentication.json. We use the conditional root exposure and test independence in the earlier variance manuscript, deletion.tex, lem:conditional-product and lem:root-flip-tests, and its weighted incidence/collision bounds, occupation.tex, lem:weighted-root-counts. Their arguments are recapitulated below to specify the conditioning. The linear-3 manuscript supplies the bounded-potential design, lem:potential and lem:occupation; its general-k extension and the higher-moment deduction below are independently proved. The earlier variance theorem and its Wilson lower bound give Var(T) = Θ_{k,B}(n) for B > Uₖ, k ≥ 4, where

\[
q_k=1-2^{-k},\qquad U_k=\log2/[-\log q_k].
\]

The later linear-3 theorem supplies Var(Hₙ) = Θ(n) for k = 3. No source theorem about a Gaussian limit is assumed.

## 2. Paid partial theorem

**Proposition A (endpoint deletion moments).** For every fixed k ≥ 3 and B > 0, there is C_{k,B} < ∞ such that, uniformly in n ≥ k, 1 ≤ i ≤ ⌊Bn⌋, and the fixed value c of Cᵢ,

\[
\mathbb E[D_i^{\,k-1}\mid C_i=c]\le C_{k,B}.                 \tag{A}
\]

Thus every fixed real p ∈ [1,k−1] has a uniformly bounded deletion p-moment. In particular k = 4 admits a uniform third moment, including all collision environments. The k = 3 endpoint overlaps the source second-moment result; it is not a new variance claim.

**Proposition B (finite range of fluctuation-scale moments).** For every fixed k ≥ 3, B > 0, and real p ∈ [2,k−1],

\[
\mathbb E|T-\mathbb ET|^p\le C_{k,B,p}n^{p/2},\qquad
\mathbb E|H_n-\mathbb EH_n|^p\le C_{k,p}n^{p/2}.             \tag{B}
\]

For the uncapped statistic the order is Θ_{k,p}(n^{p/2}) for sufficiently large n, by the stipulated linear variance lower bound and monotonicity of Lᵖ norms. The same lower order holds for the cap if B > Uₖ. The corresponding upper tail is C_{k,p}t^{-p} at t√n. This is a finite collection of polynomial bounds for a fixed k. It is **not** all-order moment control or stretched-exponential concentration, and the generic transfer from (A) to (B) is not promoted as the requested substantial discovery.

**Proposition C (Lindeberg paid for k ≥ 4).** Fix k ≥ 4 and B > Uₖ. Let ℱᵢ = σ(C₁,…,Cᵢ),

\[
M_i=\mathbb E[T\mid\mathcal F_i]-\mathbb E[T\mid\mathcal F_{i-1}],
\qquad \sigma_n^2=\operatorname{Var}(T).
\]

For every fixed ε > 0, the conditional Lindeberg sum

\[
\Lambda_n(\varepsilon)=\sigma_n^{-2}\sum_{i=1}^L
 \mathbb E[M_i^2\mathbf1_{\{|M_i|>\varepsilon\sigma_n\}}
                  \mid\mathcal F_{i-1}]
\]

converges to zero in L¹, with

\[
\mathbb E\Lambda_n(\varepsilon)
 \le C_{k,B}\varepsilon^{-(k-3)} n^{-(k-3)/2}.              \tag{C}
\]

The normalized maximal jump also tends to zero in probability. These are actual claims for the clause process, not additional assumptions.

## 3. General-k bounded potential

Work first on u ≥ k variables with an arbitrary assignment set S. Let hₐ(S) be the probability one uniform proper a-clause kills S when S is nonempty. If b coordinates are frozen throughout S, the exact formula is

\[
h_a(S)=\frac{(b)_a}{2^a(u)_a}.
\]

Set r = k−1, β = k/r. For b ≥ k, the earlier source's elementary falling-factorial comparison gives

\[
h_r(S)\le (b/(2u))^r,
\qquad
h_k(S)/h_r(S)=(b-r)/(2(u-r))\ge b/(2ku),
\]

hence hᵣ(S)^β ≤ k hₖ(S). For b < r the left side vanishes. For b = r, hₖ = 0 but

\[
h_r=\frac1{2^r\binom ur}\le(r/(2u))^r.
\]

Here binom(u,r) ≥ (u/r)^r follows by comparing each factor (u−j)/(r−j) to u/r. Consequently, for every nonempty S,

\[
h_r(S)^\beta\le k h_k(S)+e_{k,u},
\qquad e_{k,u}=(r/2)^k u^{-k}.                            \tag{1}
\]

The exceptional b = r case must not be dropped.

Let qⱼ(S) be the probability j independent proper r-clauses kill S, with q₀(S) = 0 for nonempty S and qⱼ(∅) = 1. For integer d ≥ 1 define

\[
P_d(S)=\sum_{j=0}^{d-1}q_j(S).
\]

This potential lies in [0,d] and increases when S shrinks. If Y is the subset of S surviving j fresh r-clauses and C is an independent proper k-clause, then

\[
q_{j+1}(S)-q_j(S)=\mathbb E[\mathbf1_{Y\ne\varnothing}h_r(Y)],
\]

\[
\mathbb E_C[q_j(S[C])-q_j(S)]
 =\mathbb E[\mathbf1_{Y\ne\varnothing}h_k(Y)].
\]

Jensen, (1), and the power-sum inequality for the nonnegative differences yield

\[
\mathbf1_{S\ne\varnothing}q_d(S)^\beta
 \le d^{\beta-1}
       \{k\mathbb E_C[P_d(S[C])-P_d(S)]+d e_{k,u}\}.        \tag{2}
\]

For empty S the left side is zero and monotonicity makes the right side nonnegative. This reproduces the linear-3 potential mechanism at k = 3 and extends it to fixed general k; no new claim about the truth of the upstream variance proof is involved.

## 4. Root exposure and conditional occupation

Assume n ≥ 2k and L ≥ 1; smaller n will be absorbed into a constant. Fix i and Cᵢ. Let R be its k roots, w their unique falsifying assignment, and u = n−k. Reveal through the entire cap the roots met by each other clause and their signs. Ordinary clauses meet no root and retain hidden contents. A test clause meets exactly one root and has a root literal true under w; its r nonroot literals remain hidden. All other clauses are fully exposed. Let ℰ be this static exposure, Z the number of root-incident other clauses, V the number meeting at least two roots, and d = max(1,Z).

Conditional on ℰ, ordinary contents are independent proper k-clauses on the nonroots, test contents are independent proper r-clauses there, and these collections are independent. This follows by conditioning each original independent coordinate on its root type separately: all permitted signed nonroot parts remain equiprobable. Revealing parts at the other indices preserves that product law.

Let Sₘ be the nonroot assignments satisfying the omitted prefix with roots w. Let 𝒢ₘ reveal ℰ and ordinary contents through m. Let ℋₘ additionally reveal test contents through m. Sₘ is 𝒢ₘ-measurable; the deletion event

\[
A_m=\{T\le m<T^{(i)}\},\qquad i\le m<L,
\]

is ℋₘ-measurable. Future ordinary contents are still fresh under ℋₘ. Write pₘ = q_d(Sₘ), which is nondecreasing in m.

A collision can prevent the simple flip test for at most one root: it does so only if that root is its unique root literal true under w. If V = v < k, at least j = k−v roots remain available at every time. On Aₘ each available root's independent test family must kill Sₘ, or flipping that root would yield a satisfying assignment of the restored formula. Each family has at most d clauses. Therefore

\[
\mathbb P(A_m\mid\mathcal G_m)
 \le\mathbf1_{S_m\ne\varnothing}p_m^{\,j},\quad V=v<k.     \tag{3}
\]

For m ≥ i, every nonordinary index after m meets a root, so there are at most Z such steps. Apply (2) at each ordinary step, condition on ℋₘ, sum to L−1, and telescope the nonnegative potential increments. Nonordinary summands are at most one. This proves, simultaneously for all deterministic i ≤ m < L,

\[
\mathbb E\left[\sum_{s=m}^{L-1}
       \mathbf1_{S_s\ne\varnothing}p_s^\beta
       \,\middle|\,\mathcal H_m\right]\le A,
\qquad A=a_{k,B}d^\beta,                                 \tag{4}
\]

where one explicit sufficient choice is a_{k,B} = k+1+B(k−1)^k. Indeed the ordinary contribution is at most k d^β + L d^β e_{k,u}, the nonordinary contribution at most Z ≤ d^β, and

\[
L e_{k,u}\le B(k-1)^k n^{1-k}\le B(k-1)^k.
\]

In particular, conditioning (4) down to ℰ at m = i gives

\[
\sum_{m=i}^{L-1}\mathbb E[
       \mathbf1_{S_m\ne\varnothing}p_m^\beta\mid\mathcal E]
 \le A.                                                  \tag{5}
\]

A is ℰ-measurable and stays fixed throughout the conditional argument. Test contents are not used in (4)'s bound.

## 5. Higher remaining-duration moments, without Jensen in the wrong direction

Let Nₘ = ∑_{s=m}^{L−1} 1_{Sₛ≠∅}. For pₘ > 0, monotonicity pₛ ≥ pₘ and (4) imply

\[
\mathbb E[N_m\mid\mathcal H_m]\le A p_m^{-\beta}.
\]

A first-moment bound alone does not bound higher moments. The extra fact here is that the **same bound holds at every later history**, and its upper bound decreases as p increases. For each positive integer h, induction proves

\[
\mathbb E[N_m^h\mid\mathcal H_m]
 \le h!(A p_m^{-\beta})^h.                               \tag{6}
\]

To justify the induction, for any finite zero-one sequence with remaining counts Nₛ,

\[
N_m^h\le h\sum_{s=m}^{L-1}\mathbf1_{S_s\ne\varnothing}
                         N_s^{h-1}.
\]

At an active s, Nₛ is the remaining count including s. Its possible successive values are Nₘ,…,1; the inequality is also an immediate comparison with the integral of x^{h−1}. Condition each term on ℋₛ, use the induction hypothesis and pₛ ≥ pₘ, then use the first-moment bound at m. This gives (6). The conditional tower is legitimate since ℋₘ ⊂ ℋₛ. Since Nₘ ≤ L, we also obtain

\[
\mathbb E[N_m^h\mid\mathcal H_m]\le h! W_m^h,
\quad W_m=\min\{L,A p_m^{-\beta}\},                       \tag{7}
\]

with Wₘ = L if pₘ = 0. Wₘ is 𝒢ₘ-measurable. For pₘ = 0, (7) follows just from the deterministic cap. No replacement of E[N^h] by (E[N])^h has been made.

Let Rₘ = ∑_{s=m}^{L−1}1_{Aₛ}. The same remaining-count identity gives, for integer a ≥ 2,

\[
D_i^a\le a\sum_{m=i}^{L-1}\mathbf1_{A_m}R_m^{a-1}.
\]

Rₘ ≤ Nₘ. Condition first on ℋₘ, then on 𝒢ₘ using (3) and the measurability of Wₘ, finally on ℰ. On V = v < k,

\[
\mathbb E[D_i^a\mid\mathcal E]
 \le a!\sum_{m=i}^{L-1}\mathbb E[
       \mathbf1_{S_m\ne\varnothing}p_m^j W_m^{a-1}
       \mid\mathcal E],\qquad j=k-v.                    \tag{8}
\]

When pₘ = 0 and j ≥ 1, the root-test probability is zero and the product in (8) is interpreted as zero. Thus there is no hidden division-by-zero exception.

## 6. The endpoint and every collision count

Now set a = r = k−1, so rβ = k.

**No collision, v = 0.** For p > 0,

\[
p^k W^{r-1}\le A^{r-1}p^{k-(r-1)\beta}
               =A^{r-1}p^\beta.
\]

Equation (5) gives E[Dᵢʳ | ℰ] ≤ r! Aʳ.

**1 ≤ v ≤ k−2, so j ≥ 2 > β.** The following pointwise bound handles the small-p range as well as the large-p range:

\[
p^j\min\{L,A p^{-\beta}\}^{r-1}
 \le A^{j/\beta-1}L^{r-j/\beta}p^\beta.                  \tag{9}
\]

If A ≤ L, split at p* = (A/L)^{1/β}. Below p*, divide the left side by p^β and use p^{j−β} ≤ p*^{j−β}. Above p*, use the nonpositive exponent j−rβ = −v. Both calculations give the right side. If A > L, the minimum is L for all p ≤ 1, and A^{j/β−1} ≥ L^{j/β−1}, so (9) again holds. Equation (5) and (8) now yield

\[
\mathbb E[D_i^r\mid\mathcal E]
 \le r! A^{j/\beta}L^{r-j/\beta}
 \le C_{k,B}d^{k-v}L^{v/\beta}.                          \tag{10}
\]

**v = k−1, so j = 1 < β.** Dividing by p^β would be invalid near zero. Instead bound the summand itself. Splitting at the same p*, the exponents are 1 below and 1−(r−1)β < 0 above, giving

\[
p\min\{L,A p^{-\beta}\}^{r-1}
 \le A^{1/\beta}L^{r-1-1/\beta}.
\]

The same bound follows directly when A > L. There are at most L summands in (8), so (10) also holds in this case, with d^{k−v} = d. This separate case is essential.

**V ≥ k.** Use Dᵢ ≤ L, without asserting any available root test.

We have proved the conditional endpoint bound

\[
\mathbb E[D_i^r\mid\mathcal E]
 \le C_{k,B}\left[
 d^k\mathbf1_{V=0}
 +\sum_{v=1}^{k-1}d^{k-v}L^{v/\beta}\mathbf1_{V=v}
 +L^r\mathbf1_{V\ge k}\right].                          \tag{11}
\]

To average, each other independent clause hits some root with probability ≤ k²/n and hits two roots with probability Oₖ(n⁻²). With at most Bn trials, Z has a uniformly bounded exponential moment. For every fixed nonnegative s and positive integer v,

\[
\mathbb E[d^s\mathbf1_{V\ge v}\mid C_i]
 \le C_{k,B,s,v}n^{-v}.                                 \tag{12}
\]

One direct proof expands (V)ᵥ over ordered v-tuples of distinct collision indices. Conditioning on these collisions forces v incidence indicators to one and leaves all remaining independent trials with their original laws; the conditional exponential moment of Z is at most eᵛ exp(Bk²(e−1)). Multiplying by O(n⁻²ᵛ) for each ordered tuple and O(nᵛ) tuples proves (12).

The v-th term of (11) averages to at most

\[
C_{k,B}n^{v/\beta-v}=C_{k,B}n^{-v/k};                    \tag{13}
\]

the V ≥ k term is O(n^{r−k}) = O(n⁻¹). The v = 0 term has bounded expectation. All bounds are uniform in the fixed proper clause. This proves (A) for n ≥ 2k; bounded caps cover the finitely many k ≤ n < 2k. Lower real moments follow by Jensen. Notice that collision contributions actually vanish at this endpoint; using only V ≥ 2 and the cap would have lost the third moment at k = 4.

## 7. Centered moment transfer and cap removal

Since T⁽ⁱ⁾ omits the independent coordinate Cᵢ, its Doob difference is zero. Hence

\[
M_i=-\{\mathbb E[D_i\mid\mathcal F_i]
             -\mathbb E[D_i\mid\mathcal F_{i-1}]\}.
\]

For every 1 ≤ p ≤ r, conditional Jensen and |x−y|ᵖ ≤ 2^{p−1}(|x|ᵖ+|y|ᵖ) give

\[
\mathbb E|M_i|^p\le2^p\mathbb ED_i^p\le C_{k,B,p}.       \tag{14}
\]

Here the natural clause-prefix filtration ℱᵢ differs from the root-exposure filtrations; only the already averaged bound (A) is transferred between them.

For completeness the generic centered-moment step can be proved without assuming independent Mᵢ. For p ≥ 2, Taylor's integral remainder implies

\[
|x+y|^p\le|x|^p+p x|x|^{p-2}y
               +c_p(|x|^{p-2}y^2+|y|^p).
\]

Indeed the second derivative is p(p−1)|x+ty|^{p−2}; bounding it by a constant times |x|^{p−2}+|y|^{p−2} proves the inequality. Set Sⱼ = ∑_{i≤j} Mᵢ and aⱼ = E|Sⱼ|ᵖ. The linear term has mean zero. Hölder and (14) give

\[
a_j\le a_{j-1}+c_p(K^{2/p}a_{j-1}^{1-2/p}+K),
\qquad K=\sup_i\mathbb E|M_i|^p.
\]

After division by K (the case K = 0 is trivial), induction gives aⱼ ≤ Cₚ K j^{p/2}. Choose the induction constant D with D ≥ cₚ(D^{1−2/p}+1), and compare j^{p/2}−(j−1)^{p/2} to (j−1)^{p/2−1}. This proves the capped part of (B).

For B > Uₖ, the assignment first moment gives P(Hₙ > m) ≤ 2ⁿqₖᵐ and ρ = 2qₖᴮ < 1. Put R = Hₙ − T. For every fixed p ≥ 1, the exact integer tail sum gives

\[
\mathbb ER^p
 \le q_k^{-1}\rho^n
      \sum_{j\ge0}[(j+1)^p-j^p]q_k^j
 =O_{k,B,p}(\rho^n).                                    \tag{15}
\]

The series converges. Consequently ‖R−ER‖ₚ ≤ 2‖R‖ₚ and Minkowski transfers (B) to Hₙ. No αₖn centering is introduced. The lower order follows from ‖Hₙ−EHₙ‖ₚ ≥ √Var(Hₙ) and the stipulated linear variance lower bound.

## 8. Lindeberg, realized variation, and the exact missing estimate

For k ≥ 4 take r = k−1 ≥ 3 and B > Uₖ. The source gives σₙ² = Θ(n). Using (14),

\[
\mathbb E\Lambda_n(\varepsilon)
 \le\varepsilon^{-(r-2)}\sigma_n^{-r}\sum_i\mathbb E|M_i|^r
 \le C\varepsilon^{-(r-2)}n^{1-r/2}.
\]

This proves (C), including conditional Lindeberg via convergence of a nonnegative variable in L¹. The union bound with the same r-moments gives

\[
\mathbb P(\max_i|M_i|>\varepsilon\sigma_n)
 \le C\varepsilon^{-r}n^{1-r/2}\longrightarrow0.
\]

Define

\[
v_i=\mathbb E[M_i^2\mid\mathcal F_{i-1}],\quad
Q_n=\sum_i v_i,\quad \widetilde Q_n=\sum_i M_i^2.
\]

Orthogonality gives **EQₙ = σₙ² exactly**. The outstanding sufficient estimate is

\[
\boxed{Q_n/\sigma_n^2\ \longrightarrow\ 1
          \quad\text{in probability}.}                  \tag{GAP-G}
\]

For example Var(Qₙ) = o(n²) would suffice, equivalently ∑_{i,j} Cov(vᵢ,vⱼ) = o(n²), but no such joint estimate has been proved. The marginal bound ‖vᵢ‖_{r/2} ≤ ‖Mᵢ‖ᵣ² = O(1) and EQₙ = Θ(n) do not give it. No asymptotic constant for Var(Hₙ)/n is needed if we normalize by the exact variance.

The realized/predictable distinction can also be paid. Set Yᵢ = Mᵢ²−vᵢ, a martingale difference. At k = 4, E|Yᵢ|^{3/2} = O(1) by (14). The elementary inequality for 1 < a ≤ 2,

\[
|x+y|^a\le|x|^a+a\operatorname{sgn}(x)|x|^{a-1}y+C_a|y|^a,
\]

follows by integrating the Hölder continuous signed (a−1)-power. Applying it to the martingale sum gives E|∑Yᵢ|^{3/2} = O(n). Thus

\[
\mathbb E| (\widetilde Q_n-Q_n)/\sigma_n^2 |^{3/2}
 =O(n^{-1/2})\quad(k=4).                                 \tag{16}
\]

For k ≥ 5, (14) gives uniform fourth moments, and orthogonality instead gives E(∑Yᵢ)² = O(n), so the analogous normalized second moment is O(n⁻¹). Consequently GAP-G can equivalently be replaced by concentration of the realized squared increments. Neither version has been established.

If GAP-G is proved, (C) and the triangular-array martingale CLT yield (T−ET)/σₙ ⇒ N(0,1). The precise standard criterion was read in Péter Major's authored proof notes, “Central limit theorems for martingales,” pp. 2–4, conditions (1.2)–(1.3), based on Brown (1971). Equation (15) at p = 2 and the centered L² triangle inequality give |σ(Hₙ)−σ(T)| ≤ 2‖R‖₂ = exponentially small, so the **same** standardized CLT transfers to Hₙ. This paragraph is a conditional implication, not a proved SAT CLT.

For k = 3, the endpoint is only r = 2. A bounded second moment alone does not prove Lindeberg. A sufficient additional estimate is uniform integrability of Dᵢ² over n and i; by the omission identity it would imply the corresponding uniform integrability of Mᵢ². More directly one needs Λₙ(ε) → 0, as well as GAP-G. Neither is proved for k = 3 here.

## 9. Why the all-order route remains open

The weighting in (8) at moment order a has factor p^{k−(a−1)β}; the paid occupation budget is p^β. In a collision-free environment it balances at a = k/β = k−1. For a > k−1 the small-p exponent has the wrong sign. Retaining the cap bounds the same calculation only at scale L^{a−(k−1)} times an incidence moment, not uniformly in n. This is a ceiling of this argument, not a lower bound on actual SAT moments.

One precise sufficient input for stretched-exponential concentration is all-order control of the resampling cost. Let T^[i] replace Cᵢ independently and put

\[
G_n=\sum_i\mathbb E[(T-T^{[i]})^2\mid C_1,\ldots,C_L].
\]

The omission coupling and (A) give ‖Gₙ‖_q = O(n) for fixed 1 ≤ q ≤ (k−1)/2. The sources' averaged second deletion cost provides only EGₙ = O(n). An estimate of the form

\[
\|G_n\|_q\le C n q^a\quad\text{for every real }q\ge1,
\]

with fixed finite a ≥ 0 and C independent of n,q, would, by Boucheron–Bousquet–Lugosi–Massart Theorem 2 applied to both signs, give ‖T−ET‖ₚ ≤ C'√n p^{(a+1)/2} for all p ≥ 2 and a stretched-exponential tail with exponent 2/(a+1). Such all-order cost control is **missing**. The first-moment survival tail beyond Bn does not supply it in the central window.

## 10. Structural checks and limits of inference

**Exact vanishing of first-order clause projections.** For any i and any bounded measurable g, E[g(Hₙ) | Cᵢ] = E g(Hₙ); the same holds for T. A permutation of variables and independent global sign changes acts transitively on proper signed clauses, preserves satisfiability of every prefix, and preserves the product law of all other clauses. It maps the conditional law at Cᵢ = c to that at Cᵢ = c′. Thus each individual clause is independent of the hitting-time statistic. In particular the first-order Hoeffding projection of T vanishes identically. This rules out a first-order projection-dominance proof; it does not rule out a Gaussian limit generated by many higher-order components.

**Order matters.** On any fixed k variables, take the 2ᵏ proper clauses, one falsified by each root assignment, and one extra duplicate. Listing all distinct clauses first has H = 2ᵏ; placing the duplicate before the last distinct clause has H = 2ᵏ+1. Both are admissible positive-probability clause lists. Thus the capped hitting functional is not invariant under arbitrary permutations of its clause coordinates, even though the inputs are exchangeable. The argument above uses variable/sign symmetries, never that false permutation assertion.

**Logical countermodel, not a SAT counterexample.** Let εᵢ be independent fair signs, Wₙ = |∑_{i≤n} εᵢ|, and Wₙ⁽ⁱ⁾ = |∑_{j≠i} εⱼ|+1. This omission variable dominates Wₙ and omits εᵢ; its delay is in [0,2]. Hence every deletion moment is bounded. Global sign reversal also makes Wₙ independent of each individual εᵢ, so its first-order projections vanish. The elementary iid CLT and E(∑εᵢ)⁴ = 3n²−2n show

\[
\operatorname{Var}(W_n)/n\to1-2/\pi,\qquad
\frac{W_n-\mathbb EW_n}{\sqrt{\operatorname{Var}(W_n)}}
 \Rightarrow\frac{|Z|-\sqrt{2/\pi}}{\sqrt{1-2/\pi}},
\]

which is not Gaussian. Uniform fourth moments justify the moment passages. This establishes that even much stronger abstract omission bounds and first-order degeneracy do not prove a CLT. It makes no assertion that SAT has this law.

No substantial fluctuation theorem is certified this round. The paid advance is the endpoint deletion-moment bound and its use to remove Lindeberg from the k ≥ 4 Gaussian checklist. The remaining estimate GAP-G concerns correlations between conditional increments under the real clause process. The all-order concentration route has the separate missing cost estimate above. Neither variance order, fixed-level Wilson separation, computability of α₃, nor the sharpness examples for arbitrary assignment sets close those gaps.
