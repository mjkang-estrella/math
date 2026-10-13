# I319 — exact calculations and the unpaid necessity step

Date: 2026-10-13. Research checkpoint, not a proposed complete capacity theorem. The accepted count remains fourteen toward twenty. All trees below are deterministic and locally finite; this includes the requested bounded-degree class. No numerical scan is used.

## 1. Normalization and conventions

Encode the three spins as $1,\omega,\omega^2$, $\omega^3=1$, and put
\[
 P_v=\prod_{e\in[\rho,v]}\lambda_e,\quad r_e=\lambda_e^2,
 \quad R_v=P_v^2,\quad
 a_e=\frac{1-r_e}{R_w}\quad(e=(v,w)).
\]
For the posterior $p$, write $\zeta=p_0+\omega p_1+\omega^2p_2$. The information used here is
\[
 m=E|\zeta|^2=\frac32E\sum_i(p_i-1/3)^2\in[0,1].
\]
The expected posterior chi-squared divergence from uniform is (2m). This factor matters in quantitative comparisons. The source's `fnd:norms` gives $m/\sqrt3\le E\mathrm{TV}\le(2/3)\sqrt m$. At deterministic vertices the finite-depth information decreases by data processing and has a limit. The same reverse-martingale argument as `fnd:limit` applies using the decreasing sigma-fields of all observations at distances at least (n). It supplies distinct limiting laws at distinct vertices, not a common fixed point.

Use only conserved flows of finite mass. Conservation applies at every nonroot vertex, including a leaf, so finite branches carry zero flow. The zero flow has potential zero. On a finite tree capacity is zero; take the supremum of its empty family of nonnegative ray potentials as zero. Infinite capacity means arbitrarily large **finite** admissible masses, not an infinite-mass flow.

The candidate is exactly the ordinary electrical $L^2$ capacity with resistances $a_e$: its potential is $\sup_\xi\sum_{e\in\xi}a_e\theta(e)$, linear in flow. For constant $0<\lambda<1$, it is $1/(1-\lambda^2)$ times the unweighted capacity with resistances $\lambda^{-2|w|}$. The exponent is one in the ray potential; replacing it with squared flows would be the different $L^3$ problem.

Here is also a direct exhaustion justification, including zero resistances. On the finite tree stopped at level (n), flows terminate there and vanish on earlier dead ends. If a branch's subtree has capacity (c) and its first-edge resistance is (a), the maximum branch mass is $c/(1+ac)$; when $a=0,c=\infty$, it is infinite. Parallel branch capacities add. These same series and parallel laws define electrical conductance. With resistances normalized relative to vertex $v$, the finite recursion is
\[
 c_v^{(n)}=\sum_{w\in\mathrm{ch}(v)}
 \frac{r_e c_w^{(n)}}{1+(1-r_e)c_w^{(n)}}.                 \tag{1}
\]
Terminal labels are infinity; an early empty observation has label zero. Interpret a summand with $c_w=\infty,r_e<1$ as $r_e/(1-r_e)$. The finite root capacities decrease with (n). Their limit equals the infinite-flow definition: restriction proves one direction; for any finite mass (A) below the limit, take finite admissible flows of mass (A), extract a diagonal subsequence since each edge flow lies in ([0,A]), and pass conservation and each finite ray-prefix constraint to the limit. Local finiteness ensures these are finite sums. Nonnegative prefix sums then give the full ray constraint. No optimizer at infinity is assumed.

For an infinite ray, a conserved flow is constant and
\[
 \sum_{j=1}^n a_j=R_n^{-1}-1.
\]
If $R_\infty=\lim_nR_n$, then
\[
 C_2=\frac{R_\infty}{1-R_\infty},\qquad
 m_\infty=R_\infty,\qquad
 E\mathrm{TV}_\infty=\frac23\sqrt{R_\infty}.             \tag{2}
\]
Use $C_2=0$ at $R_\infty=0$ and $C_2=\infty$ at $R_\infty=1$. The endpoint channel is the channel with parameter $P_n$, proving the posterior assertions. Perfect edges contribute exactly zero resistance. A wholly perfect ray reveals the root at every level and has infinite capacity. A perfect tail after a noisy finite prefix has finite capacity, determined by that prefix; it does not automatically give infinite capacity.

In fact, on a locally finite tree, $C_2=\infty$ iff there is a wholly perfect ray from the root. If none exists, the root's connected component using only perfect edges is finite by König's lemma. Its finitely many outgoing noisy edges form a cut for every possible positive flow, and each has admissible flow at most $R_w/(1-r_e)$. Their finite sum bounds capacity. Conversely a perfect ray carries arbitrary finite mass at zero potential. Thus infinite capacity has $m_\infty=1$, with no convention ambiguity.

## 2. Proved sufficiency, with its exact dimensionless lower bound

**Proposition.** For every locally finite tree with known independent three-state channels $0<\lambda_e\le1$,
\[
 m_\infty\ \ge\ \frac{C_2}{1+C_2},                    \tag{3}
\]
where the fraction is zero at zero capacity and one at infinite capacity. In particular, positive capacity implies reconstruction. This is a linear-estimator argument, not the requested nonlinear necessity bridge.

**Proof.** Take any admissible flow of finite positive mass (A). At level (n), define the observable
\[
 L_n=\sum_{|v|=n}\frac{\theta(v)}{P_v}S_v,
\]
where $\theta(v)$ is incoming flow. Conservation gives $\sum_{|v|=n}\theta(v)=A$ and $E[L_n\mid S_\rho]=AS_\rho$. Define edge innovations $\epsilon_w=S_w-\lambda_e S_v$. They have zero conditional mean and conditional squared modulus $1-r_e$. Distinct innovations are orthogonal: use conditional independence for siblings and conditional mean zero for an edge below another edge. They are also orthogonal to $S_\rho$. Expanding spins along their paths and using conservation yields
\[
 L_n=AS_\rho+\sum_{|w|\le n}\frac{\theta(w)}{P_w}\epsilon_w,
 \quad E|L_n|^2=A^2+\sum_{|w|\le n}a_e\theta(w)^2.       \tag{4}
\]
Normalize flow to a probability measure on rays. The energy sum in (4) equals
\[
 A E_{\mathrm{ray}}\sum_{|w|\le n}a_e\theta(w)\le A.
\]
Consequently $E[L_n\overline{S_\rho}]=A$ and conditional expectation followed by Cauchy–Schwarz gives
\[
 A^2=|E[L_n\overline{\zeta_n}]|^2
 \le E|L_n|^2m_n\le(A^2+A)m_n.
\]
Pass to the information limit and then take admissible masses tending to capacity. This proves (3). Perfect-edge innovations have zero variance, so the proof includes them without taking a channel approximation. ∎

This is the three-state eigenfunction version of the electrical linear-estimator method of Evans–Kenyon–Peres–Schulman, Theorem 1.2 and its variance/flow proof. The pinned three-state source also uses the same projection method in `fnd:supercritical`, for regular/Poisson trees. Neither fact supplies necessity for three states. No attenuated revealing scheme is needed to pay the sufficiency direction here.

## 3. Exact mixed-posterior identity

Let $\mu,\nu$ be any permutation-invariant balanced three-state posterior laws, with independent marginal complex means $u,v$. They describe observations independent conditional on the common uniform spin. Define
\[
 a=E|u|^2,\quad b=E|v|^2,\quad
 h_\mu=E\Re(u^3),\quad h_\nu=E\Re(v^3),
\]
\[
 s=u\bar v+\bar u v,\quad Z=1+s,\quad
 N=u+v+\bar u\bar v.
\]
The Bayes product has marginal tilt $Z$, posterior complex mean (N/Z), and $0\le Z\le3$. Set the weighted integrand to zero at $Z=0$. Feasibility gives $|N|\le Z$, so all the following weighted terms extend continuously at zero normalizers.

**Exact identity.**
\[
 m(\mu\star\nu)
 =a+b-ab-2(h_\mu b+a h_\nu)
   +\mathcal R(\mu,\nu),\qquad
 \mathcal R=E\frac{|N|^2s^2}{1+s}\ge0.                 \tag{5}
\]

**Proof.** Threefold rotation and reflection give $Eu=Eu^2=0$, $Eu^3=h_\mu\in\mathbb R$, and the corresponding identities for $v$. Expanding the polynomial gives
\[
 E|N|^2=a+b+ab,\qquad
 E[|N|^2s]=2ab+2(h_\mu b+a h_\nu).
\]
For instance, $E s^2=2ab$. In the cubic terms, $u^2v\cdot u\bar v$ contributes $h_\mu b$; its conjugate contributes the same quantity. The analogous two terms contribute $2a h_\nu$. All other terms have a nontrivial rotation factor in at least one independent vector. Now use $1/(1+s)=1-s+s^2/(1+s)$. At $Z=0$, $N=0$, and $|N|^2/Z\le Z$, which validates the extension. ∎

The desired quadratic saving $m(\mu\star\nu)\le a+b-cab$ is **equivalent** to
\[
 \mathcal R(\mu,\nu)
 \le (1-c)ab+2(h_\mu b+a h_\nu).                      \tag{U}
\]
It must hold for mixed laws in a class containing revealing and uninformative laws and preserved under positive channel operations and finite conditional products. Proving $U$ on that generated class, or producing a comparably useful changed potential, is the precise unpaid step. The negative source's `loc:pair` permits distinct messages but specifically smooths one message by a negative channel in ([-1/2,0]). It cannot be substituted for $U$ in the ferromagnetic recursion.

## 4. Exact refutations of overly broad versions of the route

Let $Q$ be the symmetric posterior law uniform on the three permutations of ((0,1/2,1/2)). It is the experiment that reports a uniformly chosen label different from the spin. It is balanced and has $m(Q)=1/4$, $h(Q)=-1/8$. Under independent marginal observations, the reported labels agree with probability (1/3), with tilt (3/2), and differ with probability (2/3), with tilt (3/4). Under the actual joint marginal each case therefore has probability (1/2). The posterior remains an exclusion in the first case, and reveals the spin in the second. Hence
\[
 m(Q\star Q)=\frac58>\frac12=2m(Q),\qquad
 \mathcal R(Q,Q)=\frac1{16}.                          \tag{6}
\]
Even subadditivity fails, so symmetry and balance alone cannot pay necessity.

This is not just a zero-coordinate phenomenon. The uniform orbit of ((1/9,4/9,4/9)), called $Q^\circ$, is strictly interior and has
\[
 m(Q^\circ)=1/9,\qquad m(Q^\circ\star Q^\circ)=23/99,
 \quad m(Q^\circ\star Q^\circ)-2m(Q^\circ)=1/99.        \tag{7}
\]
One symbolic verification uses the orbit of a single three-state channel with parameter $t\in(-1/2,1)$. Its product information is
\[
 M(t)=\frac{t^2}{3}
 \left[\frac{(2+t)^2}{1+2t^2}+\frac{2(1-t)}{1+t}\right],
 \quad 2t^2-M(t)=\frac{t^4(1+5t)}{(1+t)(1+2t^2)}.       \tag{8}
\]
Take $t=-1/3$ for (7), or $t=-1/2$ for (6). These experiments use a negative observation channel; they are **not** established as finite boundary laws of a tree with exclusively positive broadcast channels. Thus (6)–(7) do not refute the target or $U$ on the smallest positive-channel/product-generated class. They do refute a class closed under all symmetric degradations of revealing experiments, because such degradations already include $Q$.

Moreover, let $Q_\epsilon=(1-\epsilon)U+\epsilon Q$, with an observed independent Bernoulli mixing label and $U$ uninformative. For every $0<\epsilon\le1$,
\[
 m(Q_\epsilon)=\epsilon/4,\quad
 m(Q_\epsilon\star Q_\epsilon)=\epsilon/2+\epsilon^2/8. \tag{9}
\]
Both input moments can be arbitrarily small, while their saving is negative. The interior construction likewise gives $2\epsilon/9+\epsilon^2/99$. An expected-information-small hypothesis alone therefore does not imply strict subadditivity on all symmetric laws. This agrees with, and is stronger in its sign specificity than, the general almost-subadditivity estimate in Gu–Polyanskiy, Lemma 20; it does not contradict that estimate.

## 5. A genuinely proved local saving, and its closure obstruction

**Lemma.** If $|u|,|v|\le1/10$ almost surely, then
\[
 m(\mu\star\nu)\le a+b-\tfrac12ab.                   \tag{10}
\]
**Proof.** For general $\delta<1/\sqrt2$ with these support bounds, $|h_\mu|\le\delta a$, $|h_\nu|\le\delta b$, $Z\ge1-2\delta^2$, and $|N|\le2\delta+\delta^2$. Since $E s^2=2ab$, (5) implies
\[
 m(\mu\star\nu)\le a+b-
 \left[1-4\delta-\frac{2(2\delta+\delta^2)^2}{1-2\delta^2}\right]ab.
\]
At $\delta=1/10$, the bracket is exactly $51/100\ge1/2$. ∎

The support class is preserved under every positive channel, but **not** under products. Combine two single-channel experiments with parameter (1/10). On equal reported labels, an event with positive joint probability, the output amplitude is
\[
 \frac{2/10+1/100}{1+2/100}=\frac7{34}>\frac1{10}.
\]
Their posterior supports leave the class after one product. Revealing observations do not belong to it either. Thus (10) is not a global class mechanism. Arbitrarily weak leaf observations or small average information do not establish the uniform support hypothesis at all ancestors.

## 6. Conditional nonlinear extraction: precisely what $U$ would buy

This section is a proved **conditional implication**, not an assertion that its probabilistic hypothesis holds.

Assume there is a class as described after $U$, with a constant $0<c\le1$, such that every pair in it satisfies $d=m(\mu\star\nu)\le a+b-cab$. No common-law requirement is allowed. Put
\[
 K=c/2,\quad g(t)=t+Kt^2,\quad \kappa=K/(1+K)^2.
\]
Since $d\le a+b$,
\[
 g(d)\le a+b-cab+K(a+b)^2=g(a)+g(b).                 \tag{11}
\]
Iterate over the finitely many branches at a vertex; every partial product must stay in the class. At finite depth, then passing to the individual subtree information limits $m_v\in[0,1]$, set $y_v=g(m_v)$. Channel scaling gives
\[
 y_v\le\sum_w g(r_e m_w)
 =\sum_w r_e y_w-K\sum_w r_e(1-r_e)m_w^2
 \le\sum_w\frac{r_e y_w}{1+\kappa(1-r_e)y_w}.        \tag{12}
\]
Here $y_w\le(1+K)m_w$ and $1-t\le1/(1+t)$ for $t\ge0$. No assumption about membership of a limiting law is needed, only the finite-depth inequality.

Choose coefficients $0\le d_e\le r_e/[1+\kappa(1-r_e)y_w]$ with $y_v=\sum_wd_ey_w$, by multiplying the upper coefficients by a common ratio; choose zero coefficients when the sum is zero. Define $\ell_\rho=1$, $\ell_w=\ell_vd_e$, $\theta(e)=\ell_wy_w$, and $h_v=\ell_v/R_v$. Conservation gives a flow of mass $y_\rho$. The coefficient bound implies
\[
 \kappa(1-r_e)\frac{\theta(e)}{R_w}\le h_v-h_w.
\]
Every ray telescopes to at most $h_\rho=1$. Hence $\kappa\theta$ is admissible and
\[
 C_2\ge\kappa g(m_\infty)\ge\kappa m_\infty.         \tag{13}
\]
Under the missing hypothesis, (3) and (13) would give the exact criterion and dimensionless comparisons
\[
 \frac{C_2}{1+C_2}\le m_\infty\le\min(1,C_2/\kappa).
\]
Only the lower bound is unconditional. Equations (11)–(13) explain the quadratic change of variable and the exact channel loss $r_e-r_e^2=r_e(1-r_e)$. They do not borrow the cubic saving of the four-state preserved class. They hold with perfect edges, whose channel loss is zero, and require no bound on degrees beyond local finiteness.

## 7. Why the source does not close this step

For independent mixed positive branch laws with positive likelihoods, the additive log calculus itself does extend. With the source's $I,J,B,F=3I-2J+(4/5)B$, writing $j_i=EJ_i$ and $H$ for total correlation,
\[
 EJ_{\rm out}=\sum_i j_i,\quad
 EB_{\rm out}=\sum_i EB_i+4\sum_{i<j}j_i j_j,
\]
\[
 EF_{\rm out}=\sum_i EF_i-3H+\frac{16}{5}\sum_{i<j}j_i j_j. \tag{14}
\]
These follow by conditional independence and adding centered logs, exactly as in `pos:additive`; marginal branches are unchanged by the joint likelihood tilt. For fixed $0<\lambda<1$ and bounded degree, incoming likelihoods are bounded below, so the necessary log moments are finite even at limiting subtree laws. The source's radial inequality (`rad:lemma`) also remains valid pointwise.

However, (14) has a **positive** mixed term. The source controls it using the common-law identity $EJ=\lambda^{-2}EJ_e$, which produces `pos:Q-identities`, the region $c\nu\le\eta\le\sqrt{\mu\nu}$, and regular/Poisson factorial-moment bounds in `pos:correlation-bound`. At an arbitrary vertex there are different child laws, and there is no identity $j_v=\lambda^{-2}j_e$ for each child. Additivity only gives a sum over children. The source's fixed-point moment region cannot be asserted separately for those laws. Thus neither (14), the radial inequality, nor `loc:gap` supplies $U$ or a proved substitute. An upper information comparison and necessity remain open in this round even for one fixed $0<\lambda<1$ on arbitrary bounded-degree trees.

## 8. Validation and limits

The algebra in (5) was checked symbolically with a standard-library polynomial dictionary in formal variables $u,\bar u,v,\bar v$. The only rotationally surviving monomials of $|N|^2(1-s)$, with exponent order $(u,\bar u,v,\bar v)$, are

```
(1,1,0,0): +1      (0,0,1,1): +1      (1,1,1,1): -1
(3,0,1,1): -1      (0,3,1,1): -1
(1,1,3,0): -1      (1,1,0,3): -1
```

Exact rational Bayes-product evaluations of three preselected pairs independently checked (5): exclusion/exclusion gives $(a,b,d,\mathcal R)=(1/4,1/4,5/8,1/16)$; the interior exclusion pair gives ((1/9,1/9,23/99,16/2673)); positive single channels (1/2,1/4) give ((1/4,1/16,23/80,9/640)). These are finite identity checks, not a parameter search. The local coefficient (51/100) and support failure (7/34) were checked with `fractions.Fraction`. SymPy was unavailable; the check was completed without installing anything. All infinite arguments rest on the written proofs, not these checks.

Correctness: (1)–(10), the normalizations, and the conditional extraction are proved here. The hypothesized class inequality $U$ is unproved on positive tree-generated laws. Contribution: the useful output is an exact obstruction specification and a local partial; the flow sufficiency and capacity formalism are standard. Priority: global chi-squared non-subadditivity is already discussed in Gu–Polyanskiy, and no worldwide priority claim is made for these illustrative rational examples or the local estimate. No complete new target theorem, accepted finding, publication, or change to acceptance is proposed.
