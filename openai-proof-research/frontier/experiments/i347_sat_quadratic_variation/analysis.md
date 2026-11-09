# I347 — predictable variation: validated inputs, a two-root partial, and the unpaid covariance

Date: 2026-10-13. **Finite research endpoint; SAT CLT unresolved and not refuted.**

## 1. Model and quantifiers

Fix an integer k ≥ 4 and a real B > U_k = log(2)/[−log(1−2^(−k))]. Independently sample uniform signed proper k-clauses C₁,C₂,… on n ≥ k variables, with replacement between clauses and distinct variables within each clause. Let H be the first unsatisfiable prefix index, L = floor(Bn), T = min(H,L), and ℱ_i = σ(C₁,…,C_i). Write

\[
g_i=E[T\mid\mathcal F_i],\quad M_i=g_i-g_{i-1},\quad
v_i=E[M_i^2\mid\mathcal F_{i-1}],\quad Q=\sum_{i=1}^L v_i,
\quad \sigma^2=\operatorname{Var}(T)=\Theta_{k,B}(n).
\]

The last equality is the stipulated pinned variance theorem, whose actual statement was read. All asymptotics keep k and B fixed. Constants below may depend on them. The target is Q/σ² → 1 in probability, without presuming that σ²/n has a limit. No replacement of EH by α_k n is made.

All five finalized I343 input hashes match the supplied detached hashes. Their text and manifest were read. The upstream truth convention does not certify their new deductions; the needed proof is rederived in Section 2. Pinned manuscript paths and actual reading ranges are recorded in input-authentication.json. No sibling iteration is used.

## 2. Independent validation of the needed I343 partial

Set r = k−1 and β = k/r. Omit a clause without renumbering retained indices, let T^(i) be the resulting capped hitting time, and D_i = T^(i)−T ≥ 0. The needed claim is

\[
\sup_{n\ge k,\ 1\le i\le L,\ c}\ E[D_i^r\mid C_i=c]<\infty. \tag{2.1}
\]

Here and below a supremum over an empty index range has no obligation. D_L = 0.

### Potential and the exceptional frozen set

For a nonempty assignment set S on u ≥ k coordinates, with b coordinates constant on S, one proper a-clause kills S with probability

\[
h_a(S)=(b)_a/[2^a(u)_a].
\]

For b ≥ k, h_r^(1/r) ≤ b/(2u), while h_k/h_r = (b−r)/(2(u−r)) ≥ b/(2ku). Thus h_r^β ≤ k h_k. For b < r the left side is zero. For b = r, h_k = 0 and h_r = [2^r binom(u,r)]^(−1) ≤ [r/(2u)]^r. Consequently

\[
h_r(S)^\beta\le k h_k(S)+e_{k,u},\qquad e_{k,u}=(r/2)^k u^{-k}. \tag{2.2}
\]

Let q_d(S) be the killing probability of d independent proper r-clauses and P_d(S) = Σ_{a=0}^{d−1}q_a(S), with q_a(∅) = 1 and q₀(S) = 0 for S nonempty. If Y survives a fresh a-clause test block, then

\[
q_{a+1}(S)-q_a(S)=E[1_{Y\ne\varnothing}h_r(Y)],\qquad
E_C[q_a(S[C])-q_a(S)]=E[1_{Y\ne\varnothing}h_k(Y)].
\]

Conditional Jensen, (2.2), and the nonnegative power-sum inequality give

\[
1_{S\ne\varnothing}q_d(S)^\beta
\le d^{\beta-1}\{kE_C[P_d(S[C])-P_d(S)]+d e_{k,u}\}. \tag{2.3}
\]

The potential is monotone as S shrinks and lies in [0,d]. This is a verified general-k extension of the linear-3 source operation, not an appeal to I343 authority.

### Two filtrations and occupation

Condition on C_i = c. Its k roots have falsifying assignment w. For n ≥ 2k let u = n−k. Through the entire cap, expose the roots and root signs of every other clause. Leave ordinary clauses (no root) hidden. Leave the nonroot parts of test clauses (one root whose literal is true at w) hidden. Fully expose the others. Call this static information ℰ; let Z count root-incident clauses, V count clauses meeting at least two roots, and d = max(1,Z).

Conditioning each original coordinate separately preserves a product law: hidden ordinary clauses are uniform proper k-clauses on u coordinates; hidden test parts are uniform proper r-clauses there, independent across indices and from ordinary contents. Let S_m be the solution set of the omitted prefix with roots w. Let 𝒢_m reveal ℰ and ordinary contents through m; let ℋ_m additionally reveal past test parts. S_m is 𝒢_m-measurable, whereas A_m = {T ≤ m < T^(i)} is ℋ_m-measurable. Future ordinary contents remain fresh under ℋ_m. Put p_m = q_d(S_m), a nondecreasing 𝒢_m-measurable process.

On A_m, every solution of the omitted prefix has roots w. A collision prevents the simple root flip for at most one root, namely its unique true root literal at w. Hence, on V = v < k, at least j = k−v independent root test families must kill S_m. Each contains at most d clauses, so

\[
P(A_m\mid\mathcal G_m)\le1_{S_m\ne\varnothing}p_m^j. \tag{2.4}
\]

At an ordinary step (2.3) pays for 1_{S_m≠∅}p_m^β by expected potential drift. Sum from any m ≥ i, condition down from ℋ_s to ℋ_m, and telescope. The nonordinary steps cost at most Z. Thus, for an ℰ-measurable A = a_{k,B}d^β,

\[
E\left[\sum_{s=m}^{L-1}1_{S_s\ne\varnothing}p_s^\beta
       \mid\mathcal H_m\right]\le A. \tag{2.5}
\]

For example a_{k,B} = k+1+B r^k suffices: the ordinary contribution is at most k d^β + L d^β e_{k,u}; u ≥ n/2 makes L e_{k,u} ≤ B r^k n^(1−k). No killing probability for the exceptional b = r case was invented.

### Remaining moments and every collision count

Let N_m = Σ_{s=m}^{L−1}1_{S_s≠∅}. If p_m > 0, (2.5) and monotonicity give E[N_m|ℋ_m] ≤ A p_m^(−β). This same estimate holds at every later history. The pathwise inequality

\[
N_m^h\le h\sum_{s=m}^{L-1}1_{S_s\ne\varnothing}N_s^{h-1}
\]

and conditional induction therefore give

\[
E[N_m^h\mid\mathcal H_m]\le h!W_m^h,\qquad
W_m=\min(L,A p_m^{-\beta}), \tag{2.6}
\]

where W_m = L when p_m = 0. Crucially W_m is 𝒢_m-measurable. This induction uses the mean bound at each future history; reversed Jensen would not prove it.

Because D_i = Σ_{m=i}^{L−1}1_{A_m}, the remaining-count inequality, (2.6), and conditioning first on ℋ_m then on 𝒢_m yield, for integer a ≥ 2 and V = v < k,

\[
E[D_i^a\mid\mathcal E]
\le a!\sum_{m=i}^{L-1}E[1_{S_m\ne\varnothing}p_m^{k-v}W_m^{a-1}\mid\mathcal E]. \tag{2.7}
\]

At a = r, the collision-free weight satisfies p^k W^(r−1) ≤ A^(r−1)p^β since rβ = k. For 1 ≤ v ≤ k−2, j = k−v ≥ 2 > β and

\[
p^j\min(L,A p^{-\beta})^{r-1}
\le A^{j/\beta-1}L^{r-j/\beta}p^\beta. \tag{2.8}
\]

Check this by splitting at p* = (A/L)^(1/β), or directly if A > L. For v = k−1, j = 1 < β, division by p^β fails; instead the summand itself is at most A^(1/β)L^(r−1−1/β), and there are at most L summands. Together with (2.5) this proves

\[
E[D_i^r\mid\mathcal E]\le C\left[
d^k1_{V=0}+\sum_{v=1}^{k-1}d^{k-v}L^{v/\beta}1_{V=v}
+L^r1_{V\ge k}\right]. \tag{2.9}
\]

For p_m = 0 each root-test product in (2.7) is zero, without a division by zero.

Each random clause has incidence probability O_k(n^(−1)) and collision probability O_k(n^(−2)). Z has a bounded exponential moment. Expanding the falling factorial (V)_v over distinct indices, conditioning on these collisions, and keeping the other independent incidence laws proves

\[
E[d^s1_{V\ge v}\mid C_i=c]\le C_{k,B,s,v}n^{-v}. \tag{2.10}
\]

This retains dependence of d and V. The v-th term in (2.9) averages to O(n^(v/β−v)) = O(n^(−v/k)); the cap-only term is O(n^(r−k)) = O(n^(−1)). The first term is bounded. Finitely many n < 2k have bounded caps. This establishes (2.1), including its conditional uniformity.

### Martingale consequences actually justified

T^(i) omits C_i, so

\[
M_i=-\{E[D_i\mid\mathcal F_i]-E[D_i\mid\mathcal F_{i-1}]\},
\qquad E|M_i|^p\le2^p E D_i^p\le C_p\quad(1\le p\le r). \tag{2.11}
\]

Thus conditional Lindeberg has expectation at most C ε^(−(r−2)) n^(1−r/2), which tends to zero for every k ≥ 4. The same moment bound pays max_i|M_i|/σ → 0. For Y_i = M_i²−v_i, the 3/2-power martingale inequality gives E|ΣY_i|^(3/2) = O(n) at k = 4. At k ≥ 5 orthogonality and fourth moments give E(ΣY_i)² = O(n). Hence realized and predictable quadratic variations differ by o_P(n), as claimed in I343.

For completeness, the centered r-moment is O(n^(r/2)). The Taylor inequality for p ≥ 2, conditional mean zero, and Hölder imply the recurrence a_j ≤ a_{j−1}+C(a_{j−1}^(1−2/p)+1) for a_j = E|Σ_{i≤j}M_i|^p; induction gives O(j^(p/2)). This validates the fourth centered moment needed below when k ≥ 5.

For q_k = 1−2^(−k), first moments give P(H > m) ≤ 2^n q_k^m. Therefore R = H−T has E R^p = O((2q_k^B)^n) for each fixed p, with floor factor at most q_k^(−1). This validates late-cap transfer and variance comparison. It is standard cap control, not the missing concentration argument.

## 3. Exact double-deletion decomposition

For distinct i,j put a = max(i,j). At a prefix m ≥ a, let s_{uv}(m) indicate satisfiability when marked clause i is present iff u = 1 and marked clause j is present iff v = 1. All other clauses and their indices are retained. Define

\[
P_m=\{s_{00}=1,s_{10}=0,s_{01}=0\},\qquad
N_m=\{s_{11}=0,s_{10}=1,s_{01}=1\},
\quad R^+_{ij}=\sum_{m=a}^{L-1}1_{P_m},\quad
R^-_{ij}=\sum_{m=a}^{L-1}1_{N_m}.
\]

P_m is **redundant killing**: either restored clause alone kills the twice-deleted formula. N_m is **cooperative killing**: both clauses together kill it, while neither alone does. Monotonicity leaves exactly these two nonzero patterns in the mixed difference. Since T = Σ_{m=0}^{L−1}1_{prefix m satisfiable},

\[
J_{ij}:=T^{(ij)}-T^{(i)}-T^{(j)}+T=R^+_{ij}-R^-_{ij}. \tag{3.1}
\]

Terms before a are identically zero. In particular R^-_{ij} ≤ min(D_i,D_j). J has no fixed sign; the hitting functional is not a submodular or supermodular deletion statistic.

## 4. A paid nonroutine two-root partial

**Proposition.** Fix k ≥ 4 and B > 0. Uniformly in n ≥ k, distinct i,j ≤ floor(Bn), and fixed proper clauses c,d with disjoint variable sets,

\[
E[(R^+_{ij})^{2(k-1)}\mid C_i=c,C_j=d]\le C_{k,B},\qquad
E[(R^-_{ij})^{k-1}\mid C_i=c,C_j=d]\le C_{k,B}. \tag{4.1}
\]

No disjointness between unmarked background clauses is assumed. This is a partial for the exact SAT process, not a generic martingale identity. No priority or acceptance claim is attached to it.

### Proof of the stronger redundant-killing moment

For n ≥ 4k use the union R of the 2k marked roots, u = n−2k ≥ n/2, and the joint falsifying assignment w. Delete both marked clauses. Expose root types of the other L−2 random clauses exactly as in Section 2. Let Z,V,d have the same meanings for this union of roots; hidden test parts are still proper r-clauses. Let S_m be the twice-deleted solution slice at w.

On P_m, every background solution falsifies both marked clauses, so all its 2k roots equal w. A flip of any available root would contradict one of the two single-clause killing assertions. Each collision blocks at most one root. Conditional on the lower filtration,

\[
P(P_m\mid\mathcal G_m)\le1_{S_m\ne\varnothing}p_m^{2k-v}
\quad(V=v<2k),\qquad p_m=q_d(S_m). \tag{4.2}
\]

There is a single common slice here. All 2k hidden test families are disjoint independent families of clause coordinates, conditional on that slice and the static exposure. This conditional claim follows from the product law, not from disjoint marked roots alone.

For m ≥ a both skipped marked indices are in the past. Every future nonordinary step is root-incident. The potential (2.3) uses clause size k, so its exponent stays β = k/(k−1), not 2k/(2k−1). It gives the occupation budget A = C_{k,B}d^β and the conditional remaining-duration induction (2.6). With b = 2r, the remaining-count inequality gives

\[
E[(R^+_{ij})^b\mid\mathcal E]
\le b!\sum_{m=a}^{L-1}E[1_{S_m\ne\varnothing}p_m^{2k-v}W_m^{b-1}\mid\mathcal E]. \tag{4.3}
\]

Now bβ = 2k. For v = 0 the summand is bounded by A^(b−1)p^β. For 1 ≤ v ≤ 2k−2, set h = 2k−v ≥ 2 > β. Splitting at (A/L)^(1/β) proves

\[
p^h W^{b-1}\le A^{h/\beta-1}L^{b-h/\beta}p^\beta.
\]

For v = 2k−1 use p W^(b−1) ≤ A^(1/β)L^(b−1−1/β), then charge at most L terms. For V ≥ 2k use the cap only. The resulting bound is

\[
E[(R^+_{ij})^b\mid\mathcal E]\le C\left[
d^{2k}1_{V=0}+\sum_{v=1}^{2k-1}d^{2k-v}L^{v/\beta}1_{V=v}
+L^b1_{V\ge2k}\right]. \tag{4.4}
\]

For a fixed union of 2k roots, the same factorial incidence argument gives E[d^s1_{V≥v}] ≤ C n^(−v), because the number of roots is fixed. Thus every intermediate collision term is O(n^(−v/k)), and the cap-only term is O(n^(2r−2k)) = O(n^(−2)). This proves the first assertion, with small n absorbed into constants.

### Proof of the cooperative moment and its limitation

Given C_i=c,C_j=d with disjoint roots, redo the single-deletion proof for i. The now fixed clause d avoids i's roots, so it imposes a deterministic monotone constraint on S_m. Its step has no fresh drift but costs at most one occupation summand. Charge it separately, enlarging A by one. All remaining random ordinary and test contents retain their product law. The collision counts and available root families are unchanged. Consequently E[D_i^r|c,d] ≤ C. Since R^-_{ij} ≤ D_i, the second assertion follows.

The proof of the 2r moment cannot be transferred to R^-: the twice-deleted background may have one group of solutions falsifying c and satisfying d, and another group falsifying d and satisfying c. It need not have any solution simultaneously falsifying both. Its solution set need not be contained in the joint w-slice. The single-root witness slices can depend on the other root set's test contents. Conditioning so that both slices are known therefore does not preserve both independent testing families. Neither a product of pivotality probabilities nor a 2k-root occupation exponent for N_m is justified.

There is an explicit admissible witness to this obstruction, even with no union-root collisions. Take disjoint roots x₁,…,x_k and y₁,…,y_k, a nonroot z, and k−2 further nonroots p₁,…,p_(k−2). Enforce each root t = z by the two binary clauses (¬t ∨ z), (t ∨ ¬z), expanding each binary clause into all 2^(k−2) proper k-clauses obtained by adding every sign pattern on the p variables. Their conjunction is exactly the binary clause: for every padding assignment one added disjunction is false. Each expanded clause meets exactly one marked root. The resulting background, with N = k·2^k clauses, has all x and y roots equal to z. Now let c = x₁ ∨ ⋯ ∨ x_k and d = ¬y₁ ∨ ⋯ ∨ ¬y_k. The background is satisfiable with either z value; either c or d alone leaves one value; their conjunction kills both. Yet the joint falsifying assignment x = 0, y = 1 has an empty background slice. Put the background before c,d, choose n large enough that L > N+2, and fill the rest of the cap with repeats of a background clause. Then V = 0 throughout the cap, T = N+2, all three omission times equal L, and J = N+2−L < 0. This is a positive-probability finite clause list in the exact model. It disproves the proposed deterministic localization of cooperative interaction to union-root collisions; it is not an asymptotic counterexample to the SAT CLT.

## 5. Ghost resampling: the mixed difference is not paid

Let c,c′ at i and d,d′ at j be independent proper clauses with a common unmarked background. Let f(c,d) be the capped hitting functional. Algebra gives

\[
f(c,d)-f(c',d)-f(c,d')+f(c',d')
=J(c,d)-J(c',d)-J(c,d')+J(c',d'). \tag{5.1}
\]

The omission-only terms cancel. Each J has the signed decomposition (3.1). The positive parts have the high moment (4.1) when the relevant roots are disjoint; the negative parts only the endpoint r-moment. Even the positive parts have a bounded moment, not an o(1) influence. The proposition therefore does not establish a small mixed resampling derivative, let alone the collective decay needed for a normal approximation.

Geometric exceptions can be removed for bounded kernels: a fixed number t of independent marked clauses have any mutual root intersection with probability at most binom(t,2)k²/n. For disjoint root sets a background clause meets two union roots with probability O_k(n^(−2)), so some such collision before L has probability O_k(n^(−1)). A bounded integrand times either exceptional indicator has expectation O(n^(−1)). These are unconditional facts. Off the exceptions, the remaining ordinary formula is still shared and can correlate pivotality globally. No independence conclusion follows.

## 6. An exact posterior-variance identity for Q

This section supplies a precise unpaid estimate, not a new concentration theorem. Put W_j = Var(T|ℱ_j). Future martingale orthogonality gives

\[
E[Q\mid\mathcal F_j]=\sum_{i\le j}v_i+W_j.
\]

Indeed E[(T−g_j)²|ℱ_j] is the expected sum of all future conditional squared increments. Also E[W_j|ℱ_{j−1}] = W_{j−1}−v_j. The Doob differences of Q are therefore

\[
Z_j=v_j+W_j-W_{j-1}=W_j-E[W_j\mid\mathcal F_{j-1}]. \tag{6.1}
\]

For a sampled prefix P = (C₁,…,C_{j−1}), independently sample c,d for clause j. Let Y be a fresh common future, and write T_c = T(P,c,Y), T_d = T(P,d,Y). Cov_Y below integrates only this future, keeping P,c,d fixed. The elementary difference-of-variances identity gives

\[
W_j(P,c)-W_j(P,d)
=\operatorname{Cov}_Y(T_c-T_d,T_c+T_d).
\]

Since T is bounded by L, all quantities here are square integrable, even at k = 4. Conditional variance over c, followed by orthogonality of (6.1), proves the exact identity

\[
\boxed{\operatorname{Var}(Q)
=\frac12\sum_{j=1}^L E_{P,c,d}
 [\operatorname{Cov}_Y(T_c-T_d,T_c+T_d)^2].} \tag{6.2}
\]

It is sufficient to prove that the sum in (6.2) is o(n²). This is exactly an L² concentration obligation for Q; L² concentration is sufficient, but is not being asserted necessary for the requested probability convergence in every k.

Let T₀ = T(P,omission,Y), D_c = T₀−T_c and D_d = T₀−T_d. Then the covariance kernel is

\[
2\operatorname{Cov}_Y(D_d-D_c,T_0)
+\operatorname{Var}_Y(D_c)-\operatorname{Var}_Y(D_d). \tag{6.3}
\]

For k ≥ 5, (2.1) pays uniform fourth delay moments. Jensen implies

\[
\sum_j E[(\operatorname{Var}_Y D_c-\operatorname{Var}_Y D_d)^2]=O(n).
\]

The triangle inequality on the direct sum of these L² spaces shows that (6.2) is o(n²) **if and only if**

\[
\sum_{j=1}^L E_{P,c,d}
[\operatorname{Cov}_Y(D_d-D_c,T_0)^2]=o(n^2),\qquad k\ge5. \tag{G1}
\]

All centering in Cov_Y is at the conditional future mean. Marginal delay bounds are not decorrelation from T₀. The available fourth centered moment E|T−ET|⁴ = O(n²), together with bounded fourth resampling moments, gives only O(n) for each squared kernel via Cauchy–Schwarz, and thus O(n²) in (6.2). It reaches the boundary and supplies no little-o. No cancellation across j is available in this nonnegative sum. At k = 4 the fourth delay moment is not paid; the original (6.2) remains valid, or one can use the bounded-kernel route next.

## 7. A bounded-kernel concentration target valid also at k = 4

For a prefix P of length i−1, independent c,d, and a common future Y define Δ_i(Y) = T(P,c,Y)−T(P,d,Y). Let ψ_K(x) = max(−K,min(x,K)), for K ≥ 1. Define

\[
v_i^{[K]}(P)=\frac12 E_{c,d}\left[(E_Y\psi_K(\Delta_i(Y)))^2\right],
\qquad Q^{[K]}=\sum_i v_i^{[K]}(C_{<i}). \tag{7.1}
\]

The untruncated expression equals v_i(P), since v_i is the variance over c of E_Y T(P,c,Y). Thus 0 ≤ v_i^[K] ≤ K²/2.

Validated deletion moments give E|Δ_i|^r ≤ C uniformly in i. To estimate the approximation error, take independent futures Y,Y′ sharing P,c,d. Each resampling difference has the same bounded marginal r-moment. The square of a conditional expectation is represented by the product of these two replicas. Pointwise,

\[
|\Delta\Delta'-\psi_K(\Delta)\psi_K(\Delta')|
\le |\Delta\Delta'|(1_{|\Delta|>K}+1_{|\Delta'|>K}).
\]

Hölder with exponent r/2 > 1 and Markov with exponent r show that each tail term has expectation at most C K^(−(r−2)). Independence of the two replicas is not assumed after averaging P,c,d; their marginal moments suffice for this Hölder bound. Consequently

\[
\sup_i E|v_i-v_i^{[K]}|\le C K^{-(k-3)},\qquad
E|Q-Q^{[K]}|\le Cn K^{-(k-3)}. \tag{7.2}
\]

This handles the k = 4 moment shortage without inventing a fourth moment. Also E(Q/n)^(r/2) ≤ C by Jensen and (2.11), so the normalized bracket has a paid moment strictly above one.

A sufficient outstanding SAT estimate is, for every fixed K ≥ 1,

\[
\boxed{\frac1{n^2}\sum_{i\ne j}
\operatorname{Cov}(v_i^{[K]},v_j^{[K]})\longrightarrow0.} \tag{G2}
\]

The diagonal contributes O(nK⁴). Hence (G2) gives Var(Q^[K]) = o(n²). For each fixed K Chebyshev pays Q^[K]−EQ^[K] = o_P(n). Equation (7.2), Markov, and the same expectation error then yield

\[
\limsup_nP(|Q-EQ|>\varepsilon n)
\le C_\varepsilon K^{-(k-3)}.
\]

Let K tend to infinity after n. Since EQ = σ² = Θ(n), this proves the target **conditionally on G2**. G2 has not been proved. It is a concrete bounded four-future-replica correlation problem: each square in (7.1) uses two conditionally independent futures, and their product uses four, with the appropriate overlapping original prefixes. Disjoint target roots and fresh future inputs do not remove those shared prefixes. Geometric exceptions can be charged as in Section 5, but covariance in the shared ordinary environment remains unpaid.

## 8. Failed closure attempts and final status

1. **Two independent root exposures.** They work jointly for P_m because all solutions lie in one fixed joint slice, yielding (4.1). They fail for N_m: making both separate witness slices measurable reveals tests needed by the other bound. The independent input law does not justify independent pivotality.
2. **Second differences supported on root collisions.** False as a deterministic support claim. Cooperative killing depends on logical relations in the unmarked formula, which can connect disjoint marked roots. Root-collision rarity removes only a geometric exceptional part of a bounded kernel.
3. **Marginal moments as concentration.** Their sharp consequence for (6.2) at k ≥ 5 is O(n²), not o(n²). The folded-normal I343 logical countermodel was checked: it has bounded omissions and zero first projections but a nonnormal limit. It concerns no SAT formula and refutes no SAT theorem.
4. **First-order projection or position symmetry.** The variable/sign action makes E[g(T)|C_i] constant for bounded g, so first-order clause projections vanish. Clause-position permutation invariance does not hold: a complete 2^k-clause family on k variables and a duplicate give different killing indices depending on order.
5. **An alternate Stein kernel.** The primary Chatterjee criterion was read. Validated cubic resampling moments make its cubic error O(n^(−1/2)); concentration of its conditional covariance kernel is still an unpaid estimate. Changing the kernel does not prove the needed SAT decorrelation.

If either a sufficient concentration estimate above or another exact-model bridge is proved, validated Lindeberg plus the standard martingale CLT and the late-cap bound give (H−EH)/sqrt(Var H) ⇒ N(0,1). This round proves neither G1 nor G2 nor the requested Q concentration. It supplies the exact identity (6.2), an all-k≥4 bounded-kernel formulation, and the new finite two-root occupation partial (4.1). Generic identities, conditional implications, and cap transfer are not counted as substantial findings. No all-k SAT CLT, restricted-k CLT, SAT counterexample, or new-to-literature theorem is certified.
