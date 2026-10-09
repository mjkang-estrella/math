# Round 5: the asymmetric operator has an ordinary invariant half-space

Date: 2026-10-08. **Candidate-specific conclusion: the exact operator $Q=S+RV$ from R4 Section 8 has a nonzero proper closed invariant subspace.** In fact its central-coordinate orbit closure is an invariant half-space. A convergent, explicitly specified annihilator proves properness. The proof uses the **infinite** normalizer $L$ to obtain quartic exponential decay for a base operator; it does not recover the failed centered reflection graph.

The argument also excludes the entire family $S+M_rV$ with arbitrary bounded measurable coordinate/base multipliers $r(x,j)$, including complex ones. This is a useful obstruction to this construction route, **not** a claimed substantial new theorem or a solution of the ordinary ISP. Literature priority is unestablished. Separate calculations below prove that $Q$ and $Q^*$ have empty point spectra. The existence proof does not depend on those calculations.

All writes are this report and `frontier/{sources,experiments}/i04_operator_asymmetric/`. No further agents, staging, commits, shared-index edits, or upstream truth audit were performed. The subsequent [independent round-6 audit](../reviews/i04-operator-asymmetric-r6.md) passes without substantive correction. Parent integration accepts the deduction as [R007](../findings/R007-bounded-multiplier-halfspaces.md); source and finite checks reproduce. This sentence records the later disposition; the original author scope above is preserved.

## 1. Exact contract, definitions, and prior-art screen

I read `AGENTS.md`, `sources/upstream.json`, the iteration instructions, both requested previous reports and the complete R4 review. Input hashes are in [input_manifest.json](../sources/i04_operator_asymmetric/input_manifest.json). The accepted revision is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

The primary manuscript is *Backward intertwiners and a transitive commutant*, under `preprints/Backward-intertwiners-and-a-transitive-commutant-September-27-2026/build/sections/`. Actual source dependencies read:

- `weights.tex`: `eq:a-plus`, `eq:a-minus`, `eq:bilateral-a`, the definition of $w_j$ in `prop:fibers`, `eq:a-error`, and `prop:normquasi`.
- `intertwiner.tex`: `eq:b-recursion`, `eq:b-positive`, `eq:b-negative`, `lem:normalization`, `eq:commuting-coefficients`, `eq:V-definition`, and `prop:V`.
- `introduction.tex`: `thm:direct-model`, especially its transitivity assertion; `conclusion.tex`: the ordinary-invariant-subspace and multiplier-algebra distinctions.
- The companion *Invariant projection counterexamples for every irrational rotation*, `build/00-introduction.tex`, `thm:main`, and `product-structure.tex`, `p:prop:joint-structure`. Its factor-affiliated projection conclusions do not settle ordinary subspaces of this $Q$.

Six source files were freshly retrieved from immutable raw GitHub URLs and matched the preceding source manifest's SHA-256 and Git blob SHA-1 hashes. The [upstream manifest](../sources/i04_operator_asymmetric/upstream_manifest.json) records full paths, URLs and hashes. No theorem of either accepted manuscript was audited for truth.

**Primary prior art, checked before completing the construction.** Teschl's [*Jacobi Operators and Completely Integrable Nonlinear Lattices*](https://www.mat.univie.ac.at/~gerald/ftp/book-jac/jacop.pdf), Section 1.4, Theorem 1.14 and Remark 1.15, tracks the weighted Hilbert space in a scalar Jacobi symmetrization. Sections 2.1 and 2.5, particularly (2.1)–(2.4), (2.94) and Theorem 2.12, treat Weyl resolvents and half-line polynomial cyclicity. Those self-adjoint scalar models are not a bounded similarity model for our operator-valued recurrence. Here the change by $w_j$ is only coordinatewise, and $C$ below is a weighted base translation, not a positive self-adjoint scalar. I use finite path recurrences inspired by that standard framework, with an independent convergence proof in the original norm.

For commuting/base structure, Matache's [*Operator equations and invariant subspaces*](https://lematematiche.dmi.unict.it/index.php/lematematiche/article/view/517), Le Matematiche 49 (1994), 143–147, Section 2, Lemma, Theorems 1–2 and Corollary 3, requires additional intertwining or functional equations; commutation alone is not its invariant-subspace theorem. The full scanned paper was visually read. Kubrusly's [*Equivalent invariant subspace problems*](https://jot.theta.ro/jot/archive/1997-038-002/1997-038-002-006.pdf), JOT 38 (1997), pp. 323–325, defines quasiaffine transforms using a **bounded** injective dense-range intertwiner. Those pages were visually read. We have no such bounded global coordinate normalization, and do not transfer cyclicity or subspaces across it. For a bounded intertwiner $XT=LX$, the direct pullback argument would still have to establish both nonzeroness and properness of the pulled-back subspace.

The PDFs, access errors and hashes are in [literature_manifest.json](../sources/i04_operator_asymmetric/literature_manifest.json); exact reading scope is in [primary_screen.json](../sources/i04_operator_asymmetric/primary_screen.json). No external theorem is a logical input to the construction below.

Let $X=\mathbb Z_2$ with Haar probability, $E=L^2(X)$, and $H=\ell^2(\mathbb Z;E)$, all complex. Put $\theta x=x+1$, $N_m=2^m$, $\ell_m=8^m$, $\ell_0=1$, $I_m=[\ell_{m-1},\ell_m)\cap\mathbb Z$, and $J_m=100(N_m-2)$. For every $k\in I_m$,
\[
 a_k^+(x)=10(k+1)+J_m+100T_m(x),\quad
 a_k^-(x)=10(k+1)+J_m+100(N_m-1-T_m(x)),
\]
where $T_m(x)=x\bmod 2^m$. Both $a_0^\pm=10$. Set $a_j=a_j^+$ for $j\ge0$, $a_j=a_{-j-1}^-$ for $j<0$, and $\beta_j=e^{-a_j}$. Define $w_0=1$ and $w_{j+1}=\beta_jw_j$ for **all** integers $j$.

The source recurrence is
\[
 \widetilde b_0=1,\qquad
 \widetilde b_{j+1}(x)=\widetilde b_j(x)
       \frac{\beta_{j-1}(x+1)}{\beta_j(x)},\qquad
 L(x)=\sup_{j\in\mathbb Z}\widetilde b_j(x).
\tag{1}
\]
On the specified translation-invariant conull $X_*$, $1\le L<\infty$ and $b_j=\widetilde b_j/L$; off $X_*$ take $b_j=0$. Every pointwise argument is on this common conull set. The bounded operators are
\[
 (Sf)_j(x)=\beta_{j-1}(x)f_{j-1}(x),\quad
 (Vf)_j(x)=b_{j+1}(x-1)f_{j+1}(x-1),
\]
\[
 d_j=\begin{cases}1&j\le0,\\2&j\ge1,\end{cases}
 \qquad (Rf)_j=d_jf_j,\qquad Q=S+RV.
\tag{2}
\]
Thus the $d_j$ factor belongs at the **output** coordinate. For every fixed $j$, $M_{w_j}$ is boundedly invertible on $E$; their direct sum need not be bounded or invertible on $H$.

Define
\[
 Cg(x)=\frac{e^{-10}}{L(x-1)}g(x-1).
\tag{3}
\]
This is bounded, injective and has dense range. The all-index source identity is
\[
 \frac{b_j(x)w_j(x)}{w_{j-1}(x+1)}=\frac{e^{-10}}{L(x)}.
\]
It follows by applying both recurrences, observing independence of $j$, and evaluating at $j=0$, where $w_{-1}=e^{10}$. Consequently, for $h_j=w_j^{-1}f_j$,
\[
 w_j^{-1}(Qf)_j=h_{j-1}+d_jCh_{j+1}.
\tag{4}
\]
This is a coordinate identity, not a global similarity. In particular $(h_j)$ need not be in unweighted $\ell^2$.

One surviving commutant element is $P=SV$. Since $S,V$ commute and $P$ preserves each coordinate, it commutes with scalar-coordinate $R$, hence $PQ=QP$. Normalized coordinate blocks of $P$ equal $C$. This fact guides the calculation but by itself proves neither existence nor absence of an invariant subspace.

## 2. The exact infinite normalizer gives quartic power decay

**Lemma.** With exactly (1) and (3), for every integer $n\ge0$,
\[
 \|C^n\|\le e^{-n^4}.
\tag{5}
\]

**Proof.** Fix $m\ge1$ and the positive-measure cylinder $F_m=\{T_m=2^m-1\}$. For every $x\in F_m\cap X_*$ and every $s\le m$, the residue in block $I_s$ wraps under translation by one. Thus $\Delta a_k=-100(2^s-1)$ on $I_s$. At $v=8^m$, source equation `eq:b-positive` gives
\[
 \log\widetilde b_v(x)
 =-\sum_{k=0}^{v-1}\Delta a_k(x)+a_{v-1}(x+1)-10
 \ge 700(2^m-1)8^{m-1}=:K_m.
\tag{6}
\]
The boundary term is nonnegative; all blocks omitted from the lower bound contribute nonnegatively. Hence $\log L\ge K_m$ on $F_m\cap X_*$. This is the lower bound from R4 Section 7, now used along entire translation segments.

For $n\ge2$, choose the unique $m\ge1$ with $N=2^m\le n<2N$. Among $x-1,\ldots,x-n$ at least one point has residue $N-1$ modulo $N$, for **every** $x$. All these points remain in $X_*$ when $x\in X_*$. Every other factor of $L$ is at least one. Therefore
\[
 C^ng(x)=e^{-10n}\prod_{r=1}^{n}L(x-r)^{-1}g(x-n),\qquad
 \|C^n\|\le e^{-10n-K_m}.
\]
Since
\[
 K_m=\frac{175}{2}(N-1)N^3
 \ge\frac{175}{4}N^4
 \ge\frac{175}{64}n^4>n^4,
\]
(5) follows for $n\ge2$. The cases $n=0,1$ follow from $C^0=I$ and $\|C\|\le e^{-10}$. The non-strict middle inequality is sufficient, even though $n<2N$ gives a strict version. This proves a uniform operator-norm estimate, not an almost-everywhere orbit-rate assertion. $\square$

Also, for every integer $j\ge1$, the source bound `eq:a-error` yields
\[
 \|M_{1/w_j}\|
 \le \exp\bigl(5j(j+1)+400j^{4/3}\bigr)
 \le e^{410j^2}.
\tag{7}
\]
The point is the different powers: the cost of reversing a fixed positive coordinate weight is quadratic, while enough powers of $C$ give quartic decay. No lower bound for $L^{-1}$ and no inverse of $C$ is used.

## 3. Explicit central-orbit annihilator

Define nonnegative integers $p_{n,j}$ for all $n\ge0$, $j\in\mathbb Z$ by
\[
 p_{0,j}=\mathbf1_{j=0},\qquad
 p_{n+1,j}=p_{n,j-1}+d_jp_{n,j+1}.
\tag{8}
\]
They vanish unless $|j|\le n$ and $n-j$ is even. They are the sums of weights of finite nearest-neighbor paths; a forward step has weight one and a backward step ending at $j$ has weight $d_j$. Thus
\[
 p_{n,n}=1,\qquad 0\le p_{n,j}\le4^n.
\tag{9}
\]
Indeed there are at most $2^n$ paths, each with weight at most $2^n$.

For every $u\in E$, induction using (4) gives the **finite** identity
\[
 w_j^{-1}\bigl(Q^n(u\otimes e_0)\bigr)_j
   =p_{n,j}C^{(n-j)/2}u
\tag{10}
\]
for the allowed indices, with zero at every other index. Neither spectral decomposition nor fiberwise cyclicity enters (10).

Set, recursively for every $m\ge0$,
\[
 \alpha_m=-p_{2m+1,-1}
       -\sum_{r=0}^{m-1}p_{2m+1,2r+1}\alpha_r.
\tag{11}
\]
Empty sums are zero. The first coefficients are
\[
 -1,\ 1,\ 0,\ -1,\ 0,\ 2,\ 0,\ -5,\ 0,\ 14,\ldots.
\]
The recursion, rather than an inferred closed formula, defines every coefficient. Let $A_{-1}=1$ and $A_m=1+\sum_{r=0}^m|\alpha_r|$. Then
\[
 |\alpha_m|\le4^{2m+1}A_{m-1},\qquad
 A_m\le\prod_{r=0}^m(1+4^{2r+1})
 \le 2^{m+1}4^{(m+1)^2}.
\tag{12}
\]

For every $g\in E$, define $\mathcal Jg\in H$ by
\[
 (\mathcal Jg)_{-1}=e^{-10}g,
 \qquad
 (\mathcal Jg)_{2m+1}
   =\alpha_m M_{1/w_{2m+1}}(C^*)^{m+1}g\quad(m\ge0),
\tag{13}
\]
with all other coordinates zero. In particular the order of the multiplier and the adjoint power in (13) is part of the definition.

**Convergence and boundedness.** From (5), (7) and (12), the norm of the coordinate operator at $2m+1$ is at most
\[
 t_m=2^{m+1}4^{(m+1)^2}
       \exp\bigl(410(2m+1)^2-(m+1)^4\bigr).
\tag{14}
\]
Both $\sum_m t_m$ and $\sum_m t_m^2$ converge, since $\log t_m=-(m+1)^4+O(m^2)$. Thus (13) defines a bounded linear operator $\mathcal J:E\to H$, and
\[
 \|\mathcal Jg\|\ge e^{-10}\|g\|.
\tag{15}
\]
Its range is a closed infinite-dimensional subspace. All estimates are in the original $H$ norm. Large but finite initial values of (14) do not affect convergence.

**Exact orthogonality.** Use inner products linear in the first argument. Since the $w_j$ are positive real,
\[
 \langle w_jh_j,(\mathcal Jg)_j\rangle_E
 =\langle h_j,w_j(\mathcal Jg)_j\rangle_E.
\]
For even $n$, (10) is supported at even coordinates and (13) at odd ones, so their pairing is zero. For $n=2m+1$, the $-1$ coordinate contributes
$p_{2m+1,-1}\langle C^{m+1}u,g\rangle$. The $2r+1$ coordinate, $0\le r\le m$, contributes
\[
 \alpha_rp_{2m+1,2r+1}
   \langle C^{m-r}u,(C^*)^{r+1}g\rangle
 =\alpha_rp_{2m+1,2r+1}\langle C^{m+1}u,g\rangle.
\]
The sum is zero by (11) and $p_{2m+1,2m+1}=1$. Therefore
\[
 \langle Q^n(u\otimes e_0),\mathcal Jg\rangle_H=0
 \quad\text{for every }n\ge0\text{ and every }u,g\in E.
\tag{16}
\]
Every pairing just computed contains finitely many nonzero orbit coordinates. There is no interchange of two uncontrolled infinite sums.

## 4. The ordinary invariant half-space

**Theorem for the exact candidate.** For $Q$ in (2),
\[
 \mathcal M=
 \overline{\operatorname{span}}^{\,H}
 \{Q^n(u\otimes e_0):n\ge0,\ u\in E\}
\tag{17}
\]
is a closed $Q$-invariant subspace of infinite dimension and infinite codimension.

**Proof.** It is closed by definition. Boundedness of $Q$ and its action on the generating orbits give $Q\mathcal M\subseteq\mathcal M$. It contains $E\otimes e_0$, so its dimension is infinite. Equation (16) gives $\operatorname{ran}\mathcal J\subseteq\mathcal M^\perp$, and (15) makes this an infinite-dimensional closed copy of $E$. Thus $\mathcal M$ is proper with infinite codimension. $\square$

A formula involving only bounded constraints is also available. The adjoint $F=\mathcal J^*:H\to E$ is the operator-norm-convergent row
\[
 Ff=e^{-10}f_{-1}
     +\sum_{m\ge0}\alpha_m C^{m+1}M_{1/w_{2m+1}}f_{2m+1}.
\tag{18}
\]
The convergence follows from $\sum t_m<\infty$ and each coordinate projection having norm one. It is onto, as witnessed by vectors supported at $-1$. Thus
\[
 \mathcal N=\bigcap_{n\ge0}\ker(FQ^n)
\tag{19}
\]
is another explicitly specified closed invariant half-space: it contains $E\otimes e_0$ by (16), and is contained in $\ker F$, which has infinite codimension. We have $\mathcal M\subseteq\mathcal N$; **no equality or classification is asserted**. The single kernel $\ker F$ is not asserted to be invariant.

This defeats the candidate even though the full-pair graph from R4 fails. For example $\mathcal M$ is not $S$-invariant: $S(u\otimes e_0)$ has normalized coordinate $h_1=u$ only, so its pairing with $\mathcal Jg$ is $-\langle Cu,g\rangle$. For nonzero $u$, take $g=Cu\ne0$. The result is nonzero, while $u\otimes e_0\in\mathcal M$. There is no conflict with transitivity of the larger accepted algebra or with the no-invariant-ideal property.

## 5. Why further bounded multiplier changes cannot fix this family

**Extension, with precise scope.** Let $r:X\times\mathbb Z\to\mathbb C$ be any measurable function with
\[
 B:=\operatorname*{ess\,sup}_{(x,j)}|r(x,j)|<\infty.
\]
Let $M_r$ be multiplication on $H$. For **every** such $r$, the central orbit closure for
\[
 Q_r=S+M_rV
\tag{20}
\]
is a closed invariant half-space. There is no positivity or lower-bound hypothesis on $r$ in this statement. The original $S,V,L$ remain exactly fixed.

**Proof.** Put $r_j(x)=r(x,j)$. Normalized coordinates of $Q_r$ obey
$k_j=h_{j-1}+M_{r_j}Ch_{j+1}$. Define path operators $B_{n,j}:E\to E$ by
\[
 B_{0,j}=\mathbf1_{j=0}I,\quad
 B_{n+1,j}=B_{n,j-1}+M_{r_j}CB_{n,j+1}.
\]
As before they vanish outside the allowed parity cone, $B_{n,n}=I$, and
$w_j^{-1}(Q_r^n(u\otimes e_0))_j=B_{n,j}u$. Set $K=2\max(1,B)$. Every path with endpoint $j$ has exactly $(n-j)/2$ backward factors. Modulus domination for multiplication and the positive weighted composition $C$ gives, for every $u\in E$,
\[
 |B_{n,j}u|\le K^n C^{(n-j)/2}|u|,\qquad
 |B_{n,j}^*u|\le K^n(C^*)^{(n-j)/2}|u|.
\tag{21}
\]
For the adjoint inequality reverse each path, use
$|(M_{r_j}C)^*u|=|C^*M_{\overline{r_j}}u|\le B C^*|u|$, and sum at most $2^n$ paths. No commutation of $C$ with $M_{r_j}$ is used.

Given $g\in E$, put $z_{-1}=g$, put all nonpositive coordinates other than $-1$ and all positive even coordinates equal to zero, and recursively define
\[
 z_{2m+1}=-B_{2m+1,-1}^*g
   -\sum_{r=0}^{m-1}B_{2m+1,2r+1}^*z_{2r+1}.
\tag{22}
\]
Let $A_{-1}=1$, $A_m=\prod_{s=0}^m(1+K^{2s+1})$, and $c_m=K^{2m+1}A_{m-1}=A_m-A_{m-1}$. Induction in (21)–(22) proves the sharper bound $|z_{2m+1}|\le c_m(C^*)^{m+1}|g|$, and hence
\[
 |z_{2m+1}|\le A_m(C^*)^{m+1}|g|,
 \qquad A_m\le2^{m+1}K^{(m+1)^2}.
\tag{23}
\]
For details, the leading term in (22) is bounded by $K^{2m+1}(C^*)^{m+1}|g|$. For each earlier index, (21) supplies $(C^*)^{m-r}$ and its existing bound supplies $c_r(C^*)^{r+1}$. These exponents add to $m+1$. Summing gives the scalar bound $K^{2m+1}(1+\sum_{r<m}c_r)=K^{2m+1}A_{m-1}=c_m$. This proves the induction, including its empty-sum base case.

Set $v_j=M_{1/w_j}z_j$. Equations (5), (7), (23) show that $g\mapsto v$ is bounded into $H$ by quartic decay against quadratic growth; $v_{-1}=e^{-10}g$ makes it bounded below. Pairing $Q_r^n(u\otimes e_0)$ with $v$ is zero for even $n$ by parity, and for odd $n$ exactly by (22) and $B_{n,n}=I$. Therefore the central orbit closure has an infinite-dimensional orthogonal complement, just as in Section 4. $\square$

**Construction decision.** Even breaking $[Q_r,SV]=0$ using base-dependent coefficients is insufficient: this extension still applies. The decisive mechanism is the nearest-neighbor path grading, its identity leading forward block, and the unusually small products imposed by the exact $L$. This is a proved obstruction to the whole bounded-multiplier family, not just a list of failed reflection ansatzes. I do not propose another cosmetic change. No materially different construction with a verified mechanism for escaping this obstruction and controlling ordinary invariant subspaces was established in this round. Arbitrary nonlocal perturbations, new base transports, or different normalization regimes lie outside the proof; being outside it does not make them viable ISP constructions.

## 6. Eigenvectors and adjoint kernels, checked directly for $Q$

For completeness this section closes the specific spectral gap left by R4. It is not used in Sections 2–5.

First, $0\le Q\le S+2V=T_2$. For positive bounded operators, order is preserved under taking powers in this comparison: inductively $Q^{n+1}\le T_2Q^n\le T_2^{n+1}$. The previously proved R2 Section 7.1–7.2 estimates are
\[
 \|S^n\|\le e^{-(5/2)n^2},\qquad
 \|V^n\|\le e^{5000-n^2}.
\]
Since $S$ commutes with $V$, the binomial bound and $k^2+(n-k)^2\ge n^2/2$ give
\[
 \|Q^n\|\le\|T_2^n\|\le e^{5000}3^n e^{-n^2/2}
 \quad(n\ge0).
\tag{24}
\]
This is the proved Gaussian premise already validated in R4, not a transfer of its point-spectrum argument. Hence $Q$ and $Q^*$ have no possible nonzero eigenvalue.

Here is the needed direct kernel analysis. The source drift formulas at even $x$ give
\[
 \sum_{k=0}^{n-1}\Delta a_k(x)=100(n-1),\qquad
 \sum_{k=-q}^{-1}\Delta a_k(x)=-100(q-1).
\]
Inserting them in `eq:b-positive` and `eq:b-negative`, using $L\ge1$ and `eq:a-error`, yields, at every even $x\in X_*$,
\[
 b_j(x)\le\min(1,e^{560-45|j|})\quad(j\in\mathbb Z).
\tag{25}
\]
For example the raw positive bound is $-90(j-1)+400(j-1)^{1/3}$; the negative one at $j=-q$ is $-90q+100+400q^{1/3}$. The maximum of $400t^{1/3}-45t$ on $t\ge0$ is less than $460$, proving (25). At other bases use $b_j\le1$.

If $Qf=0$, evaluating its equation at output coordinate $j+1$ gives
\[
 f_{j+2}(x-1)=\rho_j(x)f_j(x),\qquad
 \rho_j(x)=-\frac{\beta_j(x)}{d_{j+1}b_{j+2}(x-1)}.
\tag{26}
\]
All these coefficients are finite and nonzero on $X_*$. In two steps exactly one of $x-1,x-2$ is even. For every integer $j\ge0$, (25) and the lower bounds for the two $\beta$ factors imply uniformly in $x\in X_*$
\[
 \log|\rho_{j+2}(x-1)\rho_j(x)|
 \ge25j-510-800(j+2)^{1/3}-2\log2.
\tag{27}
\]
Indeed the two numerator logarithms cost at most $20j+40+400j^{1/3}+400(j+2)^{1/3}$, while the even-base reciprocal of $b$ supplies at least $45(j+2)-560$. The right side tends to $+\infty$.

Directly taking the adjoint of (2) gives
\[
 (Q^*f)_j(x)=\beta_j(x)f_{j+1}(x)
             +d_{j-1}b_j(x)f_{j-1}(x+1).
\]
If $Q^*f=0$, substitute output index $j+1$ and base $x-1$ to get
\[
 f_{j+2}(x-1)=\rho_j^*(x)f_j(x),\qquad
 \rho_j^*(x)=-\frac{d_jb_{j+1}(x-1)}{\beta_{j+1}(x-1)}.
\tag{28}
\]
For $j\le-4$, write $t=|j|$. The same even-base argument now gives
\[
 \log|\rho_{j+2}^*(x-1)\rho_j^*(x)|
 \le-25t+655+800t^{1/3}+2\log2.
\tag{29}
\]
The two reciprocal $\beta$ factors cost at most $20t-40+800t^{1/3}$, and the even-base $b$ factor contributes at most $560-45(t-3)$. The right side tends to $-\infty$. In particular (27) is greater than one for $j\ge4096$, and (29) is less than minus one for $j\le-4096$; the weaker eventual inequalities would suffice.

To turn pointwise recurrences into a Hilbert-space conclusion, fix $p\in\{0,1\}$ and set
\[
 z_k(y)=f_{2k+p}(y-k),\qquad y\in\mathbb Z_2, k\in\mathbb Z.
\]
Translation invariance of Haar measure identifies each parity part of $H$ isometrically with $L^2(\mathbb Z_2;\ell^2(\mathbb Z))$. Fubini and a countable intersection of conull sets make the recurrence and square summability hold together for almost every $y$. Equation (26) becomes a scalar recurrence $z_{k+1}=\rho_{2k+p}(y-k)z_k$. Its two-step modulus grows by at least $e$ for all sufficiently large $k$, by (27). A nonzero solution cannot be square summable at $+\infty$; nonvanishing coefficients imply that any nonzero entry propagates. Thus $\ker Q=0$.

For (28), the two-step multiplier is at most $e^{-1}$ at sufficiently negative $k$, by (29). Reversing the recurrence forces any nonzero solution to grow at least geometrically toward $-\infty$. Thus $\ker Q^*=0$ as well. Combining with (24),
\[
 \sigma_p(Q)=\sigma_p(Q^*)=\varnothing.
\tag{30}
\]
In particular $Q$ has dense range, no nonzero finite-dimensional invariant subspace, and no proper closed invariant subspace of finite codimension. The last two assertions follow respectively from finite-dimensional complex eigenvalue existence and applying it to $Q^*$ on the orthogonal complement. These statements concern all ordinary invariant subspaces of this exact $Q$ and are consistent with the explicit half-space (17).

For comparison, no nonzero proper invariant **ideal** exists: if an ideal is $Q$-invariant, positivity and solidity make it invariant under $S$ and $RV$, hence under $V$ by applying the bounded positive multiplier $R^{-1}$. Every ideal is invariant under base multipliers, so the accepted `thm:direct-model` transitivity makes it trivial. This is an ideal argument only; it supplies no substitute for (16).

## 7. Finite verification, source integrity, and exact limitations

Run from the repository root:

```sh
python frontier/experiments/i04_operator_asymmetric/check.py
python frontier/sources/i04_operator_asymmetric/verify.py
```

The exact standard-library experiment [check.py](../experiments/i04_operator_asymmetric/check.py) and [output.json](../experiments/i04_operator_asymmetric/output.json) record:

- 70,432 all-index integer-log checks of the unnormalized coordinate identity, including both negative indices and block boundaries.
- Five explicit normalizer lower bounds through coordinate $8^5=32768$, and 87,892 residue-cover checks through path length 512. The experiment uses lower bounds for the true supremum, **never** a finite substitute for $L$.
- The scalar path and annihilator recursion for powers 0 through 81, including the coefficient-size bound.
- 276 exact path-domination checks in a three-dimensional base model with noncommuting positive diagonal multipliers and a weighted cyclic base translation; 63 matrix orbit-annihilation checks and 189 original-weighted-coordinate pairings.
- Three deliberate failures at the next odd moment after truncating the constructed annihilator. These confirm that finite orthogonality alone is insufficient, and that the infinite tail is mathematically necessary in the tested models.
- 31,810 rational checks of the constants in the two kernel bounds, for absolute coordinate indices 4096 through 20000.

No finite model establishes the infinite-dimensional result. The proofs of convergence, closure, invariance and codimension are Sections 2–5; the kernel conclusion uses the uniform bounds and Fubini in Section 6. The finite matrices are transcription checks, not substitutes for the actual normalized dyadic operator.

The final [integrity record](../sources/i04_operator_asymmetric/verification.json) checks all six upstream files against the complete pinned preprint tree, all three downloaded literature PDFs, and the assigned artifact hashes. The shared iteration README changed during this round as the parent integrated other work; its updated integration entries were reread. The other five recorded input hashes still match. The original observed-input manifest is preserved rather than silently rewritten.

A final bounded literature screen revisited weighted Jacobi cyclicity and commuting-operator transfer and searched for the present normalizer/moment mechanism. It also inspected the [publisher summary of Chalendar–Partington, Chapter 9, *Moment sequences and binomial sums*](https://www.cambridge.org/core/books/abs/modern-approaches-to-the-invariantsubspace-problem/moment-sequences-and-binomial-sums/2769F2B850EFE3B43190D800E497A0E4), which explicitly places moment methods and tridiagonal operators in established invariant-subspace theory. Only that chapter's summary was accessible/read, not its complete theorems. No exact duplicate of (5), (13) or (20) was identified in the sources inspected; this is **not** a literature-priority certification. The elementary dual-orbit criterion and three-term path recurrences are standard ideas. The new-to-project work is the uniform use of this precise $L$ to make an explicit infinite annihilator converge.

**Remaining gaps and disposition.** The candidate-specific existence question for $Q$ is resolved affirmatively by (17), and bounded coordinate/base multiplier variants are excluded by (20). No classification of the entire lattice, equality in $\mathcal M\subseteq\mathcal N$, projection formula, or bounded global Jacobi similarity is proved. No next ISP counterexample with a verified new mechanism is produced. Independent review of this round now passes; new-to-literature status remains unestablished. Record this as a decisive construction obstruction and close this candidate family; do not promote it to completion of the substantial-new-progress objective.
