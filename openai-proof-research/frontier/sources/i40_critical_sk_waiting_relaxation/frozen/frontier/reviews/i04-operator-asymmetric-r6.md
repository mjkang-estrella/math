# Round 6 independent audit: asymmetric operator and all bounded local multipliers

Date: 2026-10-08. **PASS for Sections 2–5, including every bounded measurable complex multiplier $r(x,j)$. PASS for Section 6 for the exact asymmetric $Q$. No substantive mathematical correction is required.** The central-coordinate orbit closure is a closed invariant half-space for every $S+M_rV$, with the exact pinned $S,V,L$ fixed. **Close this entire bounded-multiplier construction lane as a source of ordinary-ISP counterexamples. FAIL as an ordinary-ISP counterexample, a demonstrated new-to-literature theorem, or completion of the project's substantial-progress objective.**

This is a fresh proof audit, not an inference from parent or provider status. I read `AGENTS.md`, `sources/upstream.json`, the iteration instructions, the complete round-5 report and preceding round-4 review, the actual pinned source sections below, and the preceding Gaussian estimates and their review. I reproduced the author's finite checks and added exact tests for noncommuting complex coefficients. No agents, staging, commits, or shared-file edits were made. All writes are this review and `frontier/{sources,experiments}/i04_operator_asymmetric_r6/`.

## 1. Exact contract, normalization, and conull sets: PASS

The accepted revision is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The source is *Backward intertwiners and a transitive commutant*, under `preprints/Backward-intertwiners-and-a-transitive-commutant-September-27-2026/build/sections/`:

- `weights.tex`: `eq:a-plus`, `eq:a-minus`, `eq:bilateral-a`, the all-integer definition of $w_j$ in `prop:fibers`, `eq:a-error`, and `prop:normquasi`.
- `intertwiner.tex`: `eq:b-recursion`, `eq:b-positive`, `eq:b-negative`, `lem:normalization`, `eq:commuting-coefficients`, `eq:V-definition`, and `prop:V`.
- `introduction.tex`: the actual `thm:direct-model`, including its transitive algebra; `conclusion.tex`: ordinary tails and the distinction between coordinate and base multiplier algebras.

I also read the pinned companion *Invariant projection counterexamples for every irrational rotation*, `build/00-introduction.tex`, `thm:main`, and `build/product-structure.tex`, `p:prop:joint-structure`. Its factor-affiliated projection conclusion does not exclude ordinary invariant subspaces here. Upstream theorem truth is an accepted premise; this review audits deductions from it.

Use $X=\mathbb Z_2$, $E=L^2(X)$, and $H=\ell^2(\mathbb Z;E)$. The source defines
\[
 L(x)=\sup_{j\in\mathbb Z}\widetilde b_j(x),\qquad
 b_j(x)=\widetilde b_j(x)/L(x)\quad(x\in X_*),
\]
where $X_*$ is translation-invariant and conull, $1\le L<\infty$ there, and all $b_j$ vanish off it. Every fixed $w_j$ and $1/w_j$ is bounded: it is a finite product of fixed-coordinate weights or reciprocals. Their direct sums are not asserted to be bounded on $H$.

The all-index identity has the correct boundary and orientation. With
\[
 D_j(x)=\frac{\widetilde b_j(x)w_j(x)}{w_{j-1}(x+1)},
\]
the two recurrences give $D_{j+1}=D_j$ for every integer $j$, and $D_0=e^{-10}$ since $w_{-1}=e^{10}$. Division by $L(x)$ gives the report's identity. Consequently
\[
 Cg(x)=\frac{e^{-10}}{L(x-1)}g(x-1),\qquad
 C^*g(x)=\frac{e^{-10}}{L(x)}g(x+1),
\]
and the normalized coordinate equation for $Q_r=S+M_rV$ is exactly
\[
 M_{1/w_j}(Q_rf)_j=h_{j-1}+M_{r_j}Ch_{j+1},
 \qquad h_j=M_{1/w_j}f_j.
\]
Here $r_j(x)=r(x,j)$ acts at the output coordinate and output base. There is no global similarity assertion and no claim that $h\in\ell^2(\mathbb Z;E)$. Both $C$ and $C^*$ are injective because their scalar weight is strictly positive a.e.; density of the range of $C$ follows. No bounded inverse is used.

For precision in the extension, fix a particular measurable $r$ with essential bound $B$. Intersect $X_*$ with all integer translates of the countably many conull sets where $|r_j|\le B$. This gives one translation-invariant conull set for all coordinates, powers, and path formulas for that $r$. It is unnecessary to choose a single pointwise representative set simultaneously for the uncountable collection of all $r$. All statements are operator identities on $L^2$; this standard clarification does not repair a gap.

## 2. Quartic decay and fixed-coordinate cost: PASS

Let $N=2^m$, $v=8^m=N^3$, and $F_m=\{T_m=N-1\}$, $m\ge1$. For $x\in F_m$, every block $I_s$, $s\le m$, wraps, so its positive-index increment is $-100(2^s-1)$. In the actual source formula
\[
 \log\widetilde b_v(x)
 =-\sum_{k=0}^{v-1}\Delta a_k(x)+a_{v-1}(x+1)-10,
\]
the final boundary term is nonnegative and the omitted lower blocks also contribute nonnegatively. Keeping only $I_m$, whose size is $7\cdot8^{m-1}$, proves
\[
 \log L(x)\ge K_m:=700(2^m-1)8^{m-1}
 =\frac{175}{2}(N-1)N^3
 \quad(x\in F_m\cap X_*).
\]
The bound uses one coefficient of the **true infinite supremum**. Neither a finite maximum nor a typical-orbit estimate is substituted for $L$.

For every $n\ge2$, choose $N\le n<2N$. Any consecutive $N$ terms among $x-1,\ldots,x-n$ cover all residues modulo $N$, including $N-1$. This is true for every $x$, not merely almost every orbit eventually. Translation invariance of $X_*$ keeps the selected point in the valid set. All other $L$-factors are at least one. Thus
\[
 C^ng(x)=e^{-10n}\prod_{s=1}^nL(x-s)^{-1}g(x-n),\qquad
 \|C^n\|\le e^{-10n-K_m}.
\]
Since $N\ge2$,
\[
 K_m\ge\frac{175}{4}N^4
 \ge\frac{175}{64}n^4>n^4.
\]
The cases $n=0,1$ are $\|I\|=1$ and $\|C\|\le e^{-10}\le e^{-1}$. Therefore the stated uniform estimate $\|C^n\|\le e^{-n^4}$ passes for every integer $n\ge0$. The same norm estimate holds for $(C^*)^n$.

For $j\ge1$, `eq:a-error` gives directly
\[
 -\log w_j(x)=\sum_{k=0}^{j-1}a_k^+(x)
 \le5j(j+1)+400\sum_{k=1}^{j-1}k^{1/3}
 \le5j(j+1)+400j^{4/3}\le410j^2.
\]
This proves the fixed-coordinate multiplier bound without any implicit constant. The $j=1$ endpoint is included. Only these positive coordinates and $1/w_{-1}=e^{-10}$ occur in the annihilator.

## 3. Scalar path recursion and annihilator for the exact $Q$: PASS

For $d_j=1$ at $j\le0$, $d_j=2$ at $j\ge1$, the recurrence
\[
 p_{n+1,j}=p_{n,j-1}+d_jp_{n,j+1},\qquad p_{0,j}=\mathbf1_{j=0}
\]
correctly weights backward steps at their output coordinate. There are at most $2^n$ paths, each of weight at most $2^n$, so $0\le p_{n,j}\le4^n$. The parity cone is $|j|\le n$, $n-j$ even, and the unique all-forward path gives $p_{n,n}=1$. Each path to $j$ has exactly $(n-j)/2$ backward steps. Since the $d_j$ are scalars, the finite normalized orbit is
\[
 M_{1/w_j}(Q^n(u\otimes e_0))_j=p_{n,j}C^{(n-j)/2}u.
\]

The triangular definition of $\alpha_m$ is valid because its new pivot is $p_{2m+1,2m+1}=1$. In particular $\alpha_0=-1$. The coefficient list and bound in the report reproduce. If $A_{-1}=1$, $A_m=1+\sum_{s\le m}|\alpha_s|$, then
\[
 |\alpha_m|\le4^{2m+1}A_{m-1},\qquad
 A_m\le\prod_{s=0}^m(1+4^{2s+1})
 \le2^{m+1}4^{(m+1)^2}.
\]
Thus the prescribed coordinates
\[
 (\mathcal Jg)_{-1}=e^{-10}g,\qquad
 (\mathcal Jg)_{2m+1}=\alpha_mM_{1/w_{2m+1}}(C^*)^{m+1}g
\]
define a bounded operator $E\to H$. The coordinate multiplier must remain on the **left** of the adjoint power. Section 5 below supplies an explicit summable tail bound covering this case with $K=4$. The fixed coordinate at $-1$ yields $\|\mathcal Jg\|\ge e^{-10}\|g\|$; its range is closed and infinite-dimensional.

With inner products linear in the first variable, moving the positive real $w_j$ into the second factor cancels $M_{1/w_j}$. All $\alpha_m$ are real, so no conjugate coefficient is missing. Even orbits pair to zero by parity. For $n=2m+1$, the coefficient of $\langle C^{m+1}u,g\rangle$ is exactly
\[
 p_{2m+1,-1}+\sum_{s=0}^m p_{2m+1,2s+1}\alpha_s=0.
\]
This holds for **every** $u,g\in E$ and every $n\ge0$, not only one chosen central vector. Each orbit has finitely many coordinates, so this calculation makes no exchange of uncontrolled infinite sums.

## 4. Closure, invariance, and infinite codimension: PASS

The space
\[
 \mathcal M=\overline{\operatorname{span}}
 \{Q^n(u\otimes e_0):u\in E,\ n\ge0\}
\]
is closed by definition and invariant because $Q$ is bounded and advances its generating orbits. It contains $E\otimes e_0$. The annihilator identity places $\operatorname{ran}\mathcal J\subseteq\mathcal M^\perp$. Since $E=L^2(\mathbb Z_2)$ is infinite-dimensional and $\mathcal J$ is bounded below, both dimension and codimension are infinite.

The row $F=\mathcal J^*$ also has the correct reversed order:
\[
 Ff=e^{-10}f_{-1}+\sum_{m\ge0}\alpha_m C^{m+1}M_{1/w_{2m+1}}f_{2m+1}.
\]
The series converges in operator norm. It is onto by taking $f_{-1}=e^{10}h$ and all other coordinates zero. Hence $\mathcal N=\bigcap_{n\ge0}\ker(FQ^n)$ is closed, invariant, contains the central copy of $E$, and is contained in the infinite-codimensional $\ker F$. This is a second valid half-space description. Neither $\mathcal M=\mathcal N$ nor invariance of $\ker F$ alone has been proved or is needed.

The additional claim that this $\mathcal M$ is not $S$-invariant is correct: the pairing of $S(u\otimes e_0)$ with $\mathcal Jg$ is $-\langle Cu,g\rangle$, nonzero for $u\ne0$ and $g=Cu$. Thus the construction does not give a common invariant subspace for the accepted transitive algebra.

## 5. Arbitrary noncommuting complex multipliers: PASS

This is the main scope question. Fix any $r\in L^\infty(X\times\mathbb Z;\mathbb C)$, put $B=\|r\|_\infty$, and $K=2\max(1,B)\ge2$. The path recursion is
\[
 B_{0,j}=\mathbf1_{j=0}I,\qquad
 B_{n+1,j}=B_{n,j-1}+M_{r_j}CB_{n,j+1}.
\]
Each $B_{n,j}$ is bounded, the finite cone and parity statements persist, and $B_{n,n}=I$ irrespective of zeros or phases in $r$.

For each elementary backward block,
\[
 |M_{r_j}Cu|\le B C|u|,\qquad
 |(M_{r_j}C)^*u|=|C^*M_{\overline{r_j}}u|
 \le B C^*|u|.
\]
Both $C$ and $C^*$ preserve positivity. Induction down a product of blocks therefore bounds a forward path by $B^q C^q|u|$, and its **reversed adjoint product** by $B^q(C^*)^q|u|$, where $q=(n-j)/2$. The forward identity factors do not change this count. Summing at most $2^n$ paths, and using $2^nB^q\le K^n$, proves both inequalities (21). The adjoint estimate does not follow by taking adjoints of a modulus inequality; it follows from this separate product argument. No $M_{r_j}$ is commuted through $C$, and no positivity of $Q_r$ is presumed.

For $g\in E$, start with $z_{-1}=g$, take zero at all other nonpositive and all positive even coordinates, and define
\[
 z_{2m+1}=-B_{2m+1,-1}^*g
 -\sum_{s<m}B_{2m+1,2s+1}^*z_{2s+1}.
\]
This is a bounded linear function of $g$ at every fixed coordinate. It solves the next odd moment because the new leading block is $I$. Only nonnegative powers of $C^*$ enter estimates; no inversion of $C$, $M_r$, or a path block occurs.

The constants in the report sum correctly. Set
\[
 A_{-1}=1,\qquad A_m=\prod_{s=0}^m(1+K^{2s+1}),\qquad
 c_m=K^{2m+1}A_{m-1}=A_m-A_{m-1}.
\]
Assuming $|z_{2s+1}|\le c_s(C^*)^{s+1}|g|$ for $s<m$, the leading term is bounded by $K^{2m+1}(C^*)^{m+1}|g|$. The term indexed by $s$ is bounded by
\[
 K^{2m+1}c_s(C^*)^{m-s}(C^*)^{s+1}|g|
 =K^{2m+1}c_s(C^*)^{m+1}|g|.
\]
Consequently the total constant is
\[
 K^{2m+1}\left(1+\sum_{s<m}c_s\right)
 =K^{2m+1}A_{m-1}=c_m.
\]
The empty sum handles $m=0$. This is the stronger induction needed to justify summing the constants; merely bounding each prior term by an unrelated $A_s$ would not establish the displayed recurrence. The report uses the stronger induction correctly. Also $A_m\le2^{m+1}K^{(m+1)^2}$.

Here is a fully quantified convergence bound. For $k=m+1\ge1$, the operator from $g$ to $v_{2m+1}=M_{1/w_{2m+1}}z_{2m+1}$ has norm at most
\[
 t_m(K)=2^kK^{k^2}\exp\{410(2k-1)^2-k^4\}.
\]
Let $D_K=1640+\log K+\log2$. Then
\[
 \log t_m(K)\le-k^4+D_K k^2\le-\tfrac12 k^4
 \quad\text{whenever }k^2\ge2D_K.
\]
All earlier terms are finite. Thus both $\sum t_m(K)$ and $\sum t_m(K)^2$ converge for every finite $B$, however large. Embedding each coordinate map in $H$, its series converges in operator norm; alternatively the squared-tail bound proves convergence directly in $H$. In particular
\[
 \|\mathcal J_r\|\le
 \left(e^{-20}+\sum_{m\ge0}t_m(K)^2\right)^{1/2},\qquad
 \|\mathcal J_rg\|\ge e^{-10}\|g\|.
\]
This proves norm convergence in the **original coordinates**, not only coordinatewise formal convergence. The constants can be chosen uniformly over multipliers with any prescribed common finite bound $B$.

Pairing against a central orbit now gives, for odd $n=2m+1$,
\[
 \sum_j\langle B_{n,j}u,z_j\rangle
 =\left\langle u,\ B_{n,-1}^*g+
   \sum_{s=0}^{m}B_{n,2s+1}^*z_{2s+1}\right\rangle=0.
\]
All sums here are finite. Even $n$ again vanishes by parity. The bounded-below range of $\mathcal J_r$ therefore lies in the orthogonal complement of the closure of **all** central orbits. Section 4's dimension and invariance argument applies verbatim. This completes the universal extension.

Edge cases do not require hidden hypotheses. For $r=0$, all positive $z_j$ vanish, and the central orbit closure is exactly $\ell^2(\{j\ge0\};E)$: each fixed forward weight $w_j$ maps $E$ onto $E$. The negative-coordinate copy of $E$ supplies the annihilator. Zeros at selected coordinates or base sets never remove the all-forward identity pivot. Arbitrary complex phases and base dependence are covered by the two separate modulus estimates. Injectivity of $Q_r$, absence of invariant ideals, and empty point spectra are **not** asserted for this arbitrary family.

## 6. Spectral and ideal claims for the exact asymmetric $Q$: PASS

These claims are logically separate from half-space existence. The preceding round-2 Gaussian estimate for the exact $V$, audited in round 3, is correctly reused. At an even base, the exact drift sums give
\[
 b_j(x)\le\min\{1,e^{560-45|j|}\}.
\]
The elementary maximum used here is $(800/3)\sqrt{80/27}<460$. For positive $j$ the resulting bound is even $505-45j$; the negative side gives $560-45|j|$. Selecting $m=\lfloor n/2\rfloor$ successive even-base visits in a $V$-orbit and minimizing their spaced coordinate indices gives
\[
 \|V^n\|\le e^{560m-45\lfloor m^2/2\rfloor}\le e^{5000-n^2}.
\]
For the second inequality, adding $n^2$ bounds the exponent by $-18.5m^2+564m+46\le46+564^2/74<5000$. The source bound gives $\|S^n\|\le e^{-5n^2/2}$. Positivity implies $0\le Q^n\le(S+2V)^n$, and $S,V$ commute. Expanding this last power proves (24), including $n=0$. Its $n$-th root tends to zero, so neither $Q$ nor $Q^*$ has a nonzero eigenvalue.

Taking the actual adjoint gives
\[
 (Q^*f)_j(x)=\beta_j(x)f_{j+1}(x)+d_{j-1}b_j(x)f_{j-1}(x+1).
\]
Thus the kernel recurrences (26) and (28), including the output-index factors $d_{j+1}$ and $d_j$ respectively, are correct. For (27), at $j\ge0$, the two numerator costs sum to at most
\[
 20j+40+400j^{1/3}+400(j+2)^{1/3},
\]
while the even-base reciprocal $b$-factor supplies at least $45(j+2)-560$. The two $d$-factors cost at most $2\log2$. This gives the displayed lower bound $25j-510-800(j+2)^{1/3}-2\log2$.

For (29), write $t=|j|\ge4$. The reciprocal weights are indexed $j+1,j+3$, so their linear cost is $10(t-1)+10(t-3)=20t-40$; their corrections are at most $800t^{1/3}$. The even-base $b$-factor has absolute index at least $t-3$ and contributes at most $560-45(t-3)$. Hence the upper bound is exactly
\[
 -25t+655+800t^{1/3}+2\log2.
\]
The sharpened constant $655$, rather than the earlier review's looser $695$, is justified. The claimed thresholds follow analytically: for every $j\ge4096$, $(j/128)^3\ge j+2$, and $2\log2<2$. Substitution gives the required signs with room to spare. Finite samples are unnecessary for the eventual inequalities.

The change of variables $z_k(y)=f_{2k+p}(y-k)$, $p\in\{0,1\}$, is an isometry on each parity part by Haar translation invariance and Tonelli. For a fixed kernel vector, intersect the countably many translated null-set complements for its coordinate equations and square summability. The recurrence becomes $z_{k+1}(y)=\rho_{2k+p}(y-k)z_k(y)$, with the analogous adjoint formula. All coefficients are finite and nonzero on the common set. The two-step multiplier is eventually at least $e$ toward $+\infty$ for $Q$, excluding every nonzero square-summable solution; for $Q^*$ it is at most $e^{-1}$ at the negative end, forcing growth when the recurrence is reversed. Therefore both kernels are zero. This proves empty point spectra and the stated exclusions of finite-dimensional and finite-codimensional proper invariant subspaces over the complex field.

Finally, for a closed lattice ideal invariant under this positive $Q$, positivity and solidity imply invariance under $S$ and $RV$. Every ideal is stable under bounded coordinate/base multiplication, so applying $R^{-1}$ gives $V$-invariance. It is also invariant under all scalar base multipliers. Accepted `thm:direct-model` transitivity makes the ideal trivial. This is an ideal argument only; it does not contradict or prove the ordinary half-space result.

## 7. Reproduction, adversarial checks, and source integrity

From the repository root:

```sh
python frontier/experiments/i04_operator_asymmetric_r6/reproduce_original.py
python frontier/experiments/i04_operator_asymmetric_r6/independent_checks.py
python frontier/sources/i04_operator_asymmetric_r6/verify_sources.py
```

The copied original script and its [output](../experiments/i04_operator_asymmetric_r6/output.json) reproduce **byte-for-byte**. This includes all 70,432 logarithmic identities, five lower bounds for the true normalizer, 87,892 residue-cover checks, 82 scalar orbit moments, 276 finite path bounds, 63 matrix annihilation checks, 189 weighted pairings, three deliberately nonzero truncation residuals, and 31,810 kernel-constant checks. It does not write into the author's directory.

The new [independent checks](../experiments/i04_operator_asymmetric_r6/independent_checks.py) and [output](../experiments/i04_operator_asymmetric_r6/independent_output.json) record:

- Seven four-dimensional cyclic-base models: zero, the asymmetric scalar coefficient, constant imaginary coefficient, coordinate zeros, base zeros with phases, noncommuting coordinate/base complex values, and a complex coefficient with bound below one. All computations use exact Gaussian rationals.
- 1,932 path-operator bounds **and** 1,932 separate adjoint-path bounds; 77 triangular $Z_m$ domination bounds; 161 operator annihilator identities and 161 original-coordinate operator pairings. These matrix identities test every input and test vector in the finite model, not one selected pair.
- 1,932 independent original-coordinate orbit comparisons with positive diagonal coordinate weights. Deliberately reversing the adjoint block order is detected in three models; omitting complex conjugation is detected in four.
- 142,817 source-oriented all-index logarithmic identities, including negative indices and block boundaries; 71,400 fixed-coordinate inverse-weight bounds; 32,764 dyadic cover checks through modulus $8192$. Rational inequalities also check the elementary constants used in the universal kernel estimates.

**All are finite evidence, not an infinite-dimensional proof.** The cyclic finite $C$ models do not have the actual quartic decay and are not replacements for it. Integer representatives in the logarithmic tests check finite residue formulas; they need not themselves lie in $X_*$. No finite $L$ was used. Convergence, common-conull-set reasoning, closure, invariance, and infinite codimension are proved in Sections 1–6 of this review.

The independent [verification record](../sources/i04_operator_asymmetric_r6/verification.json) confirms all six source files against SHA-256, Git blob SHA-1, the complete untruncated pinned preprint tree, and fresh downloads from their immutable raw URLs. It also verifies all three cached literature PDFs and all 29 author artifact hashes. The author's historical input hash for the shared iteration README differs, as already disclosed; its other five historical input hashes agree. All ten reviewer inputs matched their observed hashes at verification. The exact reviewed bytes are recorded in [input_manifest.json](../sources/i04_operator_asymmetric_r6/input_manifest.json); final input/link checks and deliverable hashes are in [final_verification.json](../sources/i04_operator_asymmetric_r6/final_verification.json) and [artifact_manifest.json](../sources/i04_operator_asymmetric_r6/artifact_manifest.json). Hash integrity does not certify theorem truth or novelty.

## 8. Prior art, corrections, and disposition

The bounded independent [primary-source screen](../sources/i04_operator_asymmetric_r6/primary_screen.json) reread Teschl's actual scalar weighted-space symmetrization and half-line cyclicity statements, Section 1.4, Theorem 1.14/Remark 1.15, and Section 2.5, equation $2.94$/Theorem 2.12. Those statements do not justify a bounded global normalization here. See the [author-hosted book](https://www.mat.univie.ac.at/~gerald/ftp/book-jac/jacop.pdf).

Moment and tridiagonal methods are established invariant-subspace techniques; the accessible [Chalendar–Partington publisher summary](https://www.cambridge.org/core/books/abs/modern-approaches-to-the-invariantsubspace-problem/moment-sequences-and-binomial-sums/2769F2B850EFE3B43190D800E497A0E4) confirms that general context. Only its summary was read. A targeted search also located Grivaux's 2002 tridiagonal paper in the [author's publication record](https://pro.univ-lille.fr/sophie-grivaux/publications); the publisher returned 403 and HAL was inaccessible, so no full-text theorem review or duplicate determination is claimed. No external theorem is needed for this audit's proof. The six pinned sections read do not provide the exact quartic-normalizer/annihilator extension, but this limited screen does not establish literature priority.

**Exact correction list:** no substantive correction to the stated mathematics. Preserve the pointwise-adjoint proof of domination, the telescoping $c_m$ induction, and the original-coordinate order of multipliers; these are essential. If integrating the proof, the explicit conull-set and tail estimates above may replace the report's abbreviated explanations. Keep Section 6's conclusions restricted to the exact positive asymmetric $Q$; do not append them to arbitrary complex or vanishing $r$.

**Scope remaining:** no classification of the invariant-subspace lattice, equality $\mathcal M=\mathcal N$, projection formula, bounded global similarity, or literature priority is established. The theorem fixes the original forward shift, backward intertwiner, infinite normalizer, and coefficient placement $S+M_rV$. It does not cover unbounded $r$, altered weights or normalization, different transports, or arbitrary nonlocal perturbations. This review does not propose another cosmetic multiplier variant.

**Integration decision:** the exact asymmetric candidate and the entire family with arbitrary bounded measurable complex coordinate/base multipliers have explicit ordinary invariant half-spaces. Close this family as an ISP-counterexample route. Retain the result as a validated construction obstruction, without increasing the count of established substantial new-to-literature advances or declaring the original research objective complete. Parent integration and any separate commit remain outside this review.
