# Pre-window reduction of the k-SAT predictable-variation identity

Date: 2026-10-14. Scope: `openai-proof-research`, campaign `sat-covariance-discovery`.

The central limit theorem for the first unsatisfiable prefix is not proved. No counterexample to that theorem is proved. Nothing here is an acceptance, a count change, or a conditional CLT offered as a theorem. The proved statements are an energy localization for every fixed \(k\ge 4\), and, for every fixed \(k\ge 8\), an exact reduction of \(\operatorname{Var}(Q)=o(n^2)\) to one pre-window sum. That sum is still \(O(n^2)\) by Cauchy–Schwarz. No saved power \(n^{-\delta}\) is proved for it.

## 1. Quantifiers and notation

Fix an integer \(k\ge 4\) and a real \(B>U_k\), where
\[
U_k=\frac{\log 2}{-\log(1-2^{-k})}.
\]
For \(n\ge k\), let \(C_1,C_2,\ldots\) be i.i.d. uniform proper signed \(k\)-clauses on \(n\) variables: \(k\) distinct variables, fair independent signs, clauses drawn with replacement. Let \(H\) be the first \(m\ge 1\) such that \(C_1\wedge\cdots\wedge C_m\) is unsatisfiable, \(L=\lfloor Bn\rfloor\), and \(T=\min(H,L)\). Write \(\mu=\mathbb E[T]\), \(\sigma^2=\operatorname{Var}(T)\), and \(\mathcal F_i=\sigma(C_1,\ldots,C_i)\), with \(\mathcal F_0\) trivial. Set
\[
g_i=\mathbb E[T\mid\mathcal F_i],\qquad
M_i=g_i-g_{i-1},\qquad
v_i=\mathbb E[M_i^2\mid\mathcal F_{i-1}],\qquad
Q=\sum_{i=1}^L v_i.
\]
Thus \(g_0=\mu\), \(g_L=T\), and \(T-\mu=\sum_{i=1}^L M_i\). Orthogonality gives \(\mathbb E[Q]=\sigma^2\). The symbol \(\ln\) is the natural logarithm. For \(n\ge 3\),
\[
w_n=\bigl\lceil n^{1/2}(\ln n)^2\bigr\rceil,\qquad
s_n=\bigl\lfloor\mu-w_n\bigr\rfloor.
\]
Constants \(C\) may depend on \(k\) and \(B\) and on no other parameter. They are independent of \(n\), of the time index, and of any omitted clause. Asymptotics are as \(n\to\infty\) through integers \(n\ge k\), with \(k\) and \(B\) fixed.

The pinned variance theorem, read from `introduction.tex` at revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, states that for \(k\ge 4\) and \(B>U_k\) there are constants \(C_{k,B},c_k>0\) such that \(c_k n\le\sigma^2\le C_{k,B}n\) for all sufficiently large \(n\). Centering remains the finite-size mean \(\mu\). No limit of \(\sigma^2/n\) is assumed, and no Gaussian limit is stated there.

Let \(r=k-1\). Omitting clause \(i\) without renumbering produces the capped hitting time \(T^{(i)}\) and the duration \(D_i=T^{(i)}-T\ge 0\).

## 2. Checked moment input

The following bound is I347’s (2.1) and (2.11). The argument in `frontier/experiments/i347_sat_quadratic_variation/analysis.md`, Section 2, was read in full. The comparison (2.8) and the \(v=k-1\) summand bound were recomputed in this campaign and match that text. The incidence bound (2.10) was read and is used as stated there. The occupation proof is not recopied.

**Lemma 1.** For every fixed \(k\ge 3\) and \(B>0\),
\[
\sup_{n\ge k}\ \sup_{1\le i\le L}\ \sup_c\
\mathbb E[D_i^{\,r}\mid C_i=c]<\infty.
\]
If \(A=\mathbb E[D_i\mid\mathcal F_i]\) and \(B_i=\mathbb E[D_i\mid\mathcal F_{i-1}]\), the increment is \(M_i=-(A-B_i)\). For \(1\le p\le r\),
\[
\mathbb E|M_i|^p\le 2^p\,\mathbb E[D_i^p]\le C_p.
\]

The power comparison is conditional Jensen: \(\mathbb E|A|^p\le\mathbb E[D_i^p]\) and \(\mathbb E|B_i|^p\le\mathbb E[D_i^p]\), together with \(|A-B_i|^p\le 2^{p-1}(|A|^p+|B_i|^p)\). Hence the factor is \(2^p\).

The same statement applies to the process with any one fixed index already omitted. The remaining clauses are still i.i.d. uniform proper \(k\)-clauses and the cap is still \(\lfloor Bn\rfloor\). Consequently every Doob increment of an omitted hitting time \(T_0\), up to order \(r\), has an \(n\)-uniform moment, with the same dependence only on \(k\) and \(B\).

On \(\{T\le i-1\}\) with \(i\le L\), the stopped value equals \(H\) and is \(\mathcal F_{i-1}\)-measurable, so \(M_i=0\). The same holds for the increments of any omitted process \(T_0\).

I347’s conditional Lindeberg estimate, realized-versus-predictable comparison, and late-cap exponential bound were read in the same section. They are not reproved, and Lindeberg is not the missing step.

The two-root moment (4.1) of I347 is not used. The explicit cooperative-killing formula in that record, with disjoint marked roots and every root equal to a non-root witness, is not used. This argument does not place the covariance on root collisions or on a shared falsifying slice.

## 3. Centered moments

**Lemma 2.** Fix \(2\le p\le r\). There is a constant \(C_p\) such that, for the original process and for every one-clause omission process,
\[
\mathbb E|T-\mu|^p\le C_p n^{p/2},
\]
and the same bound holds for the omitted hitting time about its own mean. In particular, for \(k\ge 4\),
\[
\mathbb E|T-\mu|^3\le C n^{3/2}.
\]
For \(k\ge 5\), the fourth centered moment is \(O(n^2)\). For \(k\ge 8\), the \(r\)-th centered moment is \(O(n^{r/2})\).

**Proof.** Let \(S_j=\sum_{i=1}^j M_i\) and \(a_j=\mathbb E|S_j|^p\), so \(S_L=T-\mu\). For \(p\ge 2\) the map \(f(t)=|t|^p\) is \(C^2\), with \(f'(t)=p|t|^{p-2}t\) and \(f''(t)=p(p-1)|t|^{p-2}\). The integral remainder gives
\[
f(x+y)=f(x)+f'(x)y+\int_0^1(1-u)f''(x+uy)y^2\,du.
\]
Since \(|x+uy|\le |x|+|y|\) and \(p\ge 2\),
\[
|x+uy|^{p-2}\le 2^{p-2}\bigl(|x|^{p-2}+|y|^{p-2}\bigr).
\]
The integral of \(1-u\) equals \(1/2\), so the remainder is at most
\[
C_p'\bigl(|x|^{p-2}y^2+|y|^p\bigr),
\qquad
C_p'=\tfrac12 p(p-1)2^{p-2}.
\]
Conditional mean zero removes the linear term. Lemma 1 supplies \(K_p=\sup_i\mathbb E|M_i|^p<\infty\). Therefore
\[
a_j\le a_{j-1}+A\,a_{j-1}^{1-2/p}+B,
\]
where \(A=C_p'K_p^{2/p}\) and \(B=C_p'K_p\). The Hölder step is
\[
\mathbb E\bigl[|S|^{p-2}M^2\bigr]
\le\bigl(\mathbb E|S|^p\bigr)^{(p-2)/p}\bigl(\mathbb E|M|^p\bigr)^{2/p},
\]
with conjugate exponents \(p/(p-2)\) and \(p/2\) when \(p>2\). At \(p=2\) the recurrence is \(a_j\le a_{j-1}+C\), so \(a_j\le Cj\).

For \(p>2\), the mean-value gap is
\[
j^{p/2}-(j-1)^{p/2}=\tfrac p2\,\xi^{p/2-1}
\]
for some \(\xi\in(j-1,j)\). The exponent \(p/2-1\ge 0\), so the gap is at least \((p/2)(j-1)^{p/2-1}\). If \(A=0\), the choice \(M\ge\max(K_p,2B/p)\) closes the induction. If \(A>0\), choose \(M<\infty\) large enough that \(M\ge K_p\), \(M^{2/p}\ge\max(1,4A/p)\), and \(M\ge(B/A)^{p/(p-2)}\). Then
\[
M^{1-2/p}\bigl(\tfrac p2 M^{2/p}-A\bigr)\ge B,
\]
and \(a_j\le M j^{p/2}\) follows by induction from \(a_0=0\) and \(a_1\le K_p\). The omitted process has the same increment moment \(K_p\) and at most \(L\) steps, so the same \(M\) applies about its own mean. Since \(L\le Bn\), the stated powers of \(n\) follow.

## 4. Location of the mean

**Lemma 3.** For every \(\delta>0\) and all sufficiently large \(n\),
\[
\mu\le(U_k+\delta)n.
\]
If \(B>U_k\), then for all sufficiently large \(n\),
\[
\mu+w_n<L.
\]

**Proof.** The pinned introduction records
\[
\mathbb P(H>m)\le 2^n(1-2^{-k})^m.
\]
This is the first-moment bound: every fixed assignment is falsified by one of the \(2^k\) sign patterns, hence survives a uniform proper clause with probability \(1-2^{-k}\). Let \(q=1-2^{-k}\) and \(m_0=\lfloor(U_k+\delta)n\rfloor\). Then
\[
n\ln 2+m_0\ln q\le -c(\delta,k)\,n
\]
for large \(n\), because \(U_k\ln(1/q)=\ln 2\). Summing the geometric tail gives
\[
\mathbb E[H]\le m_0+\sum_{j\ge 0}\mathbb P(H>m_0+j)\le(U_k+\delta)n+1
\]
for large \(n\). Since \(T\le H\), the same upper bound holds for \(\mu\). Choose \(\delta=(B-U_k)/2>0\). Then \(w_n=o(n)\) forces \(\mu+w_n<Bn\) for large \(n\), and \(L=\lfloor Bn\rfloor\) lies strictly above \(\mu+w_n\).

The matching linear lower bound on \(\mu\) is a consequence of Theorem A and the pinned lower bound \(\sigma^2\ge c_k n\), recorded after that theorem. It is not taken from a threshold location \(\alpha_k\).

## 5. Energy localization

**Theorem A.** Fix \(k\ge 4\) and \(B>U_k\). For all sufficiently large \(n\),
\[
\sum_{i>\mu-w_n}\mathbb E[M_i^2]
\le C n^{1/2}(\ln n)^2.
\]
Hence
\[
\sum_{i\le s_n}\mathbb E[M_i^2]
=\sigma^2-O\bigl(n^{1/2}(\ln n)^2\bigr),
\]
the right-hand side is at least \((c_k/2)n\) for large \(n\), and \(s_n\ge c n\) for a positive \(c=c(k,B)\). In particular \(Q_{>s_n}=\sum_{i>s_n}v_i\) satisfies \(\mathbb E[Q_{>s_n}]=O(n^{1/2}(\ln n)^2)\), so \(Q_{>s_n}/n\to 0\) in \(L^1\). Therefore \(Q/\sigma^2\to 1\) in probability if and only if the pre-window sum \(Q_{\le s_n}/\sigma^2\to 1\) in probability.

**Proof.** Lemma 1 at \(p=2\) gives \(\mathbb E[M_i^2]\le K_2\). The index interval \((\mu-w_n,\mu+w_n]\) contains at most \(2w_n+2\) integers, so its contribution is at most \(K_2(2w_n+2)\). For the right tail, \(M_i=0\) on \(\{T<i\}\), and Hölder with exponents \(3/2\) and \(3\) yields
\[
\mathbb E[M_i^2]
=\mathbb E[M_i^2 1_{T\ge i}]
\le\bigl(\mathbb E|M_i|^3\bigr)^{2/3}\mathbb P(T\ge i)^{1/3}.
\]
Lemma 2 and Markov give, for \(i>\mu+w_n\) and \(t=i-\mu>w_n\),
\[
\mathbb P(T\ge i)\le C n^{3/2}/t^3,
\]
so \(\mathbb E[M_i^2]\le C n^{1/2}/t\). Summing \(t\) from \(w_n\) to \(L\) produces at most \(C n^{1/2}\ln(Bn/w_n)\le C n^{1/2}\ln n\). Adding the window gives the first display.

The pinned theorem supplies \(\sigma^2\ge c_k n\) for large \(n\). Subtracting the tail leaves at least \((c_k/2)n\) of predictable energy on \(\{1,\ldots,s_n\}\). Each summand is at most \(K_2\), so \(s_n\ge (c_k/(2K_2))n\). Nonnegativity and \(\mathbb E[Q_{>s_n}]=O(n^{1/2}(\ln n)^2)\) give the \(L^1\) convergence. Since \(\sigma^2=\Theta(n)\), the difference \(Q-Q_{\le s_n}\) is \(o_P(n)\), which is the stated equivalence for convergence in probability.

Theorem A does not bound \(\operatorname{Var}(Q)\). A nonnegative random variable of mean \(o(n)\) may still have variance of order \(n^2\). The \(L^2\) reduction begins in Section 8 and requires \(k\ge 8\).

## 6. The posterior identity, rederived

This is I347’s identity (6.2)–(6.3). The algebra is rederived here because Theorem B quotes it.

Let \(W_j=\operatorname{Var}(T\mid\mathcal F_j)\). Future-increment orthogonality gives
\[
\mathbb E[Q\mid\mathcal F_j]=\sum_{i\le j}v_i+W_j,
\]
and \(\mathbb E[W_j\mid\mathcal F_{j-1}]=W_{j-1}-v_j\). The Doob differences of the bounded random variable \(Q\) are
\[
Z_j=W_j-\mathbb E[W_j\mid\mathcal F_{j-1}],
\]
so \(\operatorname{Var}(Q)=\sum_{j=1}^L\mathbb E[Z_j^2]\).

Given a prefix \(P\) of length \(j-1\), draw \(c,d\) as i.i.d. copies of clause \(j\) and let \(Y\) be the common future \((C_{j+1},\ldots,C_L)\). Write \(T_c=T(P,c,Y)\) and \(T_d=T(P,d,Y)\). For an integrable square random variable and an independent copy, conditional variance is half the mean square difference, so
\[
\mathbb E[Z_j^2\mid\mathcal F_{j-1}]
=\tfrac12\mathbb E_{c,d}\bigl[(W_j(P,c)-W_j(P,d))^2\bigr].
\]
For the \(Y\)-law at fixed \((P,c,d)\),
\begin{align*}
\operatorname{Cov}_Y(T_c-T_d,T_c+T_d)
&=\mathbb E_Y[T_c^2-T_d^2]
-(\mathbb E_Y T_c-\mathbb E_Y T_d)(\mathbb E_Y T_c+\mathbb E_Y T_d)\\
&=\operatorname{Var}_Y(T_c)-\operatorname{Var}_Y(T_d).
\end{align*}
Therefore
\[
\operatorname{Var}(Q)
=\frac12\sum_{j=1}^L
\mathbb E_{P,c,d}\bigl[\operatorname{Cov}_Y(T_c-T_d,T_c+T_d)^2\bigr].
\tag{6.2}
\]
Let \(T_0\) be the capped hitting time with clause \(j\) omitted, and set \(D_c=T_0-T_c\), \(D_d=T_0-T_d\), and
\[
X=D_d-D_c=T_c-T_d.
\]
Then \(T_c+T_d=2T_0-D_c-D_d\). Polarization gives
\[
\operatorname{Cov}_Y(D_d-D_c,D_c+D_d)=\operatorname{Var}_Y(D_d)-\operatorname{Var}_Y(D_c),
\]
and the kernel splits as
\[
\operatorname{Cov}_Y(T_c-T_d,T_c+T_d)
=2\operatorname{Cov}_Y(X,T_0)+\rho,
\tag{6.3}
\]
where \(\rho=\operatorname{Var}_Y(D_c)-\operatorname{Var}_Y(D_d)\).

**Lemma 4.** For every fixed \(k\ge 5\), \(\sum_{j=1}^L\mathbb E[\rho^2]=O(n)\).

**Proof.** \(\operatorname{Var}_Y(D_c)\le\mathbb E_Y[D_c^2]\), so
\[
\mathbb E[\operatorname{Var}_Y(D_c)^2]
\le\mathbb E\bigl[(\mathbb E_Y D_c^2)^2\bigr]
\le\mathbb E[\mathbb E_Y D_c^4]
=\mathbb E[D_c^4].
\]
Lemma 1 supplies a uniform fourth moment because \(4\le r\). The same bound holds for \(d\), and \((a-b)^2\le 2a^2+2b^2\). Each of the \(L\) indices contributes \(O(1)\).

**Lemma 5.** For \(k\ge 5\), \(\operatorname{Var}(Q)=o(n^2)\) if and only if
\[
\sum_{j=1}^L\mathbb E\bigl[\operatorname{Cov}_Y(X,T_0)^2\bigr]=o(n^2).
\]
The equivalence is two-sided at the level of rates: if \(R_n\) denotes the sum of \(\mathbb E[\operatorname{Cov}_Y(X,T_0)^2]\), then
\[
\operatorname{Var}(Q)\le 4 R_n+O(n),
\qquad
R_n\le \operatorname{Var}(Q)+O(n).
\]

**Proof.** Let \(\kappa=\operatorname{Cov}_Y(X,T_0)\) and let \(\eta=2\kappa+\rho\) be the kernel in (6.3). Then \(\eta^2\le 8\kappa^2+2\rho^2\). In the other direction \(\kappa=(\eta-\rho)/2\) and \((\eta-\rho)^2\le 2\eta^2+2\rho^2\), so \(\kappa^2\le\tfrac12\eta^2+\tfrac12\rho^2\). Identity (6.2) is \(\operatorname{Var}(Q)=\tfrac12\sum\mathbb E[\eta^2]\). Summing and applying Lemma 4 therefore gives both displayed comparisons. The second one uses \(\sum\mathbb E[\eta^2]=2\operatorname{Var}(Q)\).

Cauchy–Schwarz stops at the same place as in I347. For \(k\ge 5\),
\[
\mathbb E[\kappa^2]
\le\bigl(\mathbb E[(X-\mathbb E_Y X)^4]\bigr)^{1/2}
\bigl(\mathbb E[(T_0-\mathbb E_Y T_0)^4]\bigr)^{1/2}.
\]
The first factor is \(O(1)\) by Lemma 1. The second is \(O(n)\) by Lemma 2. Thus each index contributes \(O(n)\), the sum of \(L\) indices is \(O(n^2)\), and the summands are nonnegative, so no cancellation across \(j\) is present in this upper bound.

## 7. Splitting one covariance at a deterministic time

Fix \(j\le s_n\). In the resampling space of Section 6, write \(Y_\le=(C_{j+1},\ldots,C_{s_n})\) and \(Y_>=(C_{s_n+1},\ldots,C_L)\), and let
\[
\mathcal G=\sigma(P,c,d,Y_\le).
\]
The clause \(j\) itself has been replaced by the pair of copies \(c,d\), or omitted for \(T_0\). Conditionally on \((P,c,d)\), the law of \(Y\) is a product of uniform proper clauses. The covariance decomposition under that law is
\begin{align*}
\kappa
&=\operatorname{Cov}_Y\bigl(\mathbb E[X\mid\mathcal G],\mathbb E[T_0\mid\mathcal G]\bigr)
+\operatorname{Cov}_Y\bigl(X-\mathbb E[X\mid\mathcal G],\,T_0-\mathbb E[T_0\mid\mathcal G]\bigr)\\
&=\alpha+\beta.
\end{align*}
Both summands are \((P,c,d)\)-measurable. The cross terms vanish because \(X-\mathbb E[X\mid\mathcal G]\) and \(T_0-\mathbb E[T_0\mid\mathcal G]\) are \(Y\)-mean zero and the conditional expectations are \(\mathcal G\)-measurable. In particular \(\mathbb E_Y[T_0-\mathbb E[T_0\mid\mathcal G]]=0\).

Let \(\nu=\mathbb E[T_0]\) and let \(M_i^0\) be the Doob increments of \(T_0\) in the omitted process. Then
\[
S:=T_0-\mathbb E[T_0\mid\mathcal G]
=\sum_{i>s_n}M_i^0.
\]
The sum on the right does not depend on \(c\) or \(d\). Also \(0\le\nu-\mu=\mathbb E[D_j]\le C\), by Lemma 1 applied in the original process.

Stopping at the random time \(T_0\) does not create this split. On \(\{m\ge T_0\}\) every one of \(T_0\), \(T_c\), and \(T_d\) has already stopped, so \(X\) is measurable at time \(T_0\) and the post-death increments are zero. The entire covariance then sits on the pre-death \(\sigma\)-field. The time \(s_n\) used here is deterministic and, by Theorem A, a linear distance \(\Theta(n)\) before \(\mu\), with only an \(n^{1/2}(\ln n)^2\) window left above it.

**Lemma 6.** For \(k\ge 5\) and \(j\le s_n\),
\[
\mathbb E[\beta^2]
\le C\bigl(\mathbb E|S|^4\bigr)^{1/2},
\]
with \(C\) independent of \(j\) and \(n\).

**Proof.** Write \(X^>=X-\mathbb E[X\mid\mathcal G]\). Then \(\beta=\operatorname{Cov}_Y(X^>,S)\) and \(\mathbb E_Y[S]=0\), so
\[
\beta^2\le\mathbb E_Y[(X^>)^2]\,\mathbb E_Y[S^2].
\]
Cauchy–Schwarz and \((\mathbb E_Y W^2)^2\le\mathbb E_Y W^4\) give
\[
\mathbb E[\beta^2]
\le\bigl(\mathbb E|X^>|^4\bigr)^{1/2}\bigl(\mathbb E|S|^4\bigr)^{1/2}.
\]
Conditional Jensen for \(t\mapsto|t|^4\) yields \(\mathbb E|\mathbb E[X\mid\mathcal G]|^4\le\mathbb E|X|^4\), hence \(\mathbb E|X^>|^4\le 16\mathbb E|X|^4\). And \(|X|\le D_c+D_d\), so Lemma 1 bounds \(\mathbb E|X|^4\) uniformly in \(j\).

## 8. Fourth moment after time \(s_n\), for \(k\ge 8\)

**Lemma 7.** Fix \(k\ge 8\) and \(B>U_k\). Uniformly in the omitted index,
\[
\mathbb E|S|^4\le C n^{3/2}(\ln n)^6
\]
for all sufficiently large \(n\). Consequently
\[
\sum_{j\le s_n}\mathbb E[\beta^2]
\le C n^{7/4}(\ln n)^3.
\]

**Proof.** Let \(M_i\) denote the increments of this fixed omitted process, and write \(K_r=\sup\mathbb E|M_i|^r<\infty\) by the inheritance statement in Lemma 1. Let \(\theta=(r-4)/r\). For \(k\ge 8\) one has \(r\ge 7\), so \(\theta\in[3/7,1)\). Hölder with exponents \(r,r,r/2,r/(r-4)\) gives, whenever \(i,j<k\),
\begin{align*}
\bigl|\mathbb E[M_i M_j M_k^2]\bigr|
&=\bigl|\mathbb E[M_i M_j M_k^2 1_{T_0\ge k}]\bigr|\\
&\le K_r^{4/r}\,\mathbb P(T_0\ge k)^\theta.
\end{align*}
The same exponent sum bounds \(\mathbb E|M_k|^4\) and \(\bigl|\mathbb E[M_i M_k^3]\bigr|\) by \(K_r^{4/r}\mathbb P(T_0\ge k)^\theta\). The indicator is legitimate because \(M_k=0\) on \(\{T_0<k\}\).

Expand \(S_{m}=S_{m-1}+M\) one index at a time. The cubic cross term has conditional mean zero, so
\[
\mathbb E|S|^4
=\sum_{k>s_n}\Bigl(
6\,\mathbb E[S_{<k}^2 M_k^2]
+4\,\mathbb E[S_{<k} M_k^3]
+\mathbb E[M_k^4]
\Bigr).
\]
The first summand inside is nonnegative. The second may be negative, and is estimated in absolute value. With \(m_k\) equal to the number of increments strictly between \(s_n\) and \(k\),
\begin{align*}
\mathbb E[S_{<k}^2 M_k^2]
&\le m_k^2 K_r^{4/r}\mathbb P(T_0\ge k)^\theta,\\
\bigl|\mathbb E[S_{<k} M_k^3]\bigr|
&\le m_k K_r^{4/r}\mathbb P(T_0\ge k)^\theta,\\
\mathbb E[M_k^4]
&\le K_r^{4/r}\mathbb P(T_0\ge k)^\theta.
\end{align*}
Also \(m_k\le k-s_n\).

Split the sum at \(\mu+w_n\). On \(s_n<k\le\mu+w_n\) there are at most \(2w_n+2\) indices, \(k-s_n\le 2w_n+2\), and the probability factor is at most 1. The resulting contribution is at most
\[
C(2w_n+2)^3\le C' n^{3/2}(\ln n)^6.
\]

On \(k>\mu+w_n\), set \(t=k-\nu\). Lemma 3 and the bound \(\nu-\mu\le C\) give \(t\ge w_n/2\) for large \(n\), and \(k-s_n\le C t\). Lemma 2 and Markov give
\[
\mathbb P(T_0\ge k)\le C n^{r/2}/t^r,
\]
hence \(\mathbb P^\theta\le C n^{(r-4)/2}/t^{r-4}\). The triple contribution of one such \(k\) is at most
\[
C t^2\cdot n^{(r-4)/2}/t^{r-4}
=C n^{(r-4)/2}\,t^{6-r}.
\]
For \(r=7\) the power of \(t\) is \(-1\), and
\[
\sum_{w_n/2\le t\le L}t^{-1}\le C\ln n,
\]
while \(n^{(r-4)/2}=n^{3/2}\). For \(r\ge 8\) the exponent \(6-r\le -2\), so
\[
\sum_{t\ge w_n/2}t^{6-r}\le C_r w_n^{7-r},
\]
and
\[
n^{(r-4)/2}w_n^{7-r}
\le C n^{(r-4)/2+(7-r)/2}(\ln n)^{2(7-r)}
=C n^{3/2}(\ln n)^{2(7-r)}.
\]
The exponent of the logarithm is negative. The cubic and quadruple far sums are of order at most \(n(\ln n)^C\) and \(n^{1/2}(\ln n)^C\) by the same estimate with one or zero factors of \(t\), both smaller than \(n^{3/2}(\ln n)^6\).

Adding these bounds gives \(\mathbb E|S|^4\le C n^{3/2}(\ln n)^6\). Lemma 6 multiplies by at most \(L\le Bn\) after the square root:
\[
\sum_{j\le s_n}\mathbb E[\beta^2]
\le Bn\cdot C n^{3/4}(\ln n)^3
=C' n^{7/4}(\ln n)^3.
\]

The exponent \(7/4\) is the window count. A bound that uses only the fourth-moment Markov estimate \(\mathbb P(|T_0-\nu|\ge t)\le C n^2/t^4\), and discards the higher moment \(r\), has far-triple order \(n^{3-2\theta}\) and final order \(n^{(5-2\theta)/2}\). That weaker majorant is \(o(n^2)\) only for \(k\ge 10\). At \(k=9\), \(\theta=1/2\) and \((5-2\theta)/2=2\). The argument above uses the paid \(r\)-moment and therefore starts at \(k=8\).

## 9. Indices after time \(s_n\)

**Lemma 8.** Fix \(k\ge 8\) and \(B>U_k\). For all sufficiently large \(n\),
\begin{align*}
\sum_{s_n<j\le\mu+w_n}\mathbb E[\kappa_j^2]
&\le C n^{3/2}(\ln n)^2,\\[4pt]
\sum_{j>\mu+w_n}\mathbb E[\kappa_j^2]
&\le C n^{3/2}.
\end{align*}

**Proof.** The window contains at most \(2w_n+2\) indices, and Section 6 gives \(\mathbb E[\kappa_j^2]\le C n\) at every \(j\) once \(k\ge 5\). The product is \(O(n w_n)\).

For the far region, \(\kappa_j=0\) unless the length-\((j-1)\) prefix is still satisfiable. That event \(A\) is a function of \(P\) alone. On \(A^c\), one has \(T_c=T_d=T_0\le j-1\), so \(X=0\). Thus \(\kappa^2=\kappa^2 1_A\). With \(U=T_0-\mathbb E_Y[T_0]\),
\[
\kappa^2\le 1_A\,\mathbb E_Y[(X-\mathbb E_Y X)^2]\,\mathbb E_Y[U^2].
\]
Cauchy–Schwarz as in Lemma 6 produces
\[
\mathbb E[\kappa^2]
\le C\bigl(\mathbb E[1_A\,\mathbb E_Y|U|^4]\bigr)^{1/2}.
\]
The prefactor \(C\) absorbs \(\mathbb E|X|^4=O(1)\). Since \(A\) is \(P\)-measurable and \(t\mapsto|t|^4\) is convex,
\[
\mathbb E\bigl[1_A|\mathbb E[T_0\mid P]-\nu|^4\bigr]
\le\mathbb E\bigl[|T_0-\nu|^4 1_A\bigr],
\]
and \(\mathbb E_Y|U|^4\le 8|T_0-\nu|^4+8|\mathbb E_Y T_0-\nu|^4\). Therefore
\[
\mathbb E[\kappa^2]\le C\bigl(\mathbb E[|T_0-\nu|^4 1_A]\bigr)^{1/2}.
\]
Hölder with exponents \(r/4\) and \(r/(r-4)\) gives
\[
\mathbb E[|T_0-\nu|^4 1_A]
\le\bigl(\mathbb E|T_0-\nu|^r\bigr)^{4/r}\mathbb P(A)^\theta
\le C n^2\,\mathbb P(T_0\ge j)^\theta.
\]
For \(j>\mu+w_n\) and \(t=j-\nu\ge w_n/2\),
\[
\mathbb P(T_0\ge j)\le C n^{r/2}/t^r,
\]
so
\[
\mathbb E[\kappa^2]
\le C n\cdot\bigl(n^{r/2}/t^r\bigr)^{\theta/2}
=C n^{1+(r-4)/4}\,t^{-(r-4)/2}.
\]
At \(r=7\) the \(t\)-power is \(-3/2\) and the \(n\)-power is \(7/4\). Then
\[
\sum_{t\ge w_n/2}t^{-3/2}\le C w_n^{-1/2}\le C n^{-1/4}(\ln n)^{-1},
\]
and the product is \(O(n^{3/2})\). At \(r>7\) the \(t\)-integral from \(w_n\) is \(O(w_n^{1-(r-4)/2})\), and the powers of \(n\) cancel to \(n^{3/2}\) times a negative power of \(\ln n\).

## 10. The reduction

**Theorem B.** Fix an integer \(k\ge 8\) and a real \(B>U_k\). For the pre-window sum
\[
\mathcal A_n
=\sum_{j=1}^{s_n}
\mathbb E\Bigl[
\operatorname{Cov}_Y\bigl(
\mathbb E[X\mid\mathcal G],\,
\mathbb E[T_0\mid\mathcal G]
\bigr)^2
\Bigr],
\]
there is a constant \(C_{k,B}\) such that, for all sufficiently large \(n\),
\begin{align*}
\operatorname{Var}(Q)
&\le 8\mathcal A_n+C_{k,B}\,n^{7/4}(\ln n)^3,\\[4pt]
\mathcal A_n
&\le 2\operatorname{Var}(Q)+C_{k,B}\,n^{7/4}(\ln n)^3.
\end{align*}
In particular \(\operatorname{Var}(Q)=o(n^2)\) if and only if \(\mathcal A_n=o(n^2)\). Since \(\mathbb E[Q]=\sigma^2\) and \(c_k n\le\sigma^2\le C_{k,B}n\) for large \(n\), the following are equivalent:

1. \(\mathcal A_n=o(n^2)\).
2. \(\operatorname{Var}(Q)=o(n^2)\).
3. \(Q/\sigma^2\to 1\) in \(L^2\), hence also in probability.

**Proof.** For \(j\le s_n\), \(\kappa=\alpha+\beta\) and \(\mathbb E[\kappa^2]\le 2\mathbb E[\alpha^2]+2\mathbb E[\beta^2]\). Summing and applying Lemmas 7 and 8,
\[
R_n
=\sum_{j=1}^L\mathbb E[\kappa_j^2]
\le 2\mathcal A_n+C n^{7/4}(\ln n)^3.
\]
The window sum \(O(n^{3/2}(\ln n)^2)\) and the far sum \(O(n^{3/2})\) are absorbed in the larger \(n^{7/4}(\ln n)^3\) term for large \(n\). In the other direction, \(\mathbb E[\alpha^2]\le 2\mathbb E[\kappa^2]+2\mathbb E[\beta^2]\), so
\[
\mathcal A_n\le 2 R_n+C n^{7/4}(\ln n)^3.
\]
Lemma 5 converts \(R_n\) into \(\operatorname{Var}(Q)\) up to an \(O(n)\) error, which is likewise absorbed. The identity \(\mathbb E[(Q-\sigma^2)^2]=\operatorname{Var}(Q)\) is the \(L^2\) statement, because \(\mathbb E[Q]=\sigma^2\).

## 11. The sum that is still open

**Proposition 9.** Under the hypotheses of Theorem B,
\[
\mathcal A_n\le C_{k,B}\,n^2
\]
for all sufficiently large \(n\). No proof is given that \(\mathcal A_n=O(n^{2-\delta})\) for any \(\delta>0\), nor that \(\mathcal A_n=o(n^2)\).

**Proof.** The conditional covariance \(\alpha\) satisfies
\[
\alpha^2
\le\operatorname{Var}_Y\bigl(\mathbb E[X\mid\mathcal G]\bigr)\,
\operatorname{Var}_Y\bigl(\mathbb E[T_0\mid\mathcal G]\bigr).
\]
The same Cauchy–Schwarz passage as in Section 6, using only \(\mathbb E|X|^4=O(1)\) and \(\mathbb E|T_0-\nu|^4=O(n^2)\), yields \(\mathbb E[\alpha^2]\le C n\). There are at most \(L\) indices in the sum, so \(\mathcal A_n=O(n^2)\). Theorem A shows that the range \(j\le s_n\) contains at least \(c n\) indices; that count is not a lower bound for \(\mathcal A_n\).

This is the same order as the I347 ceiling for the full sum (6.2). Removing the post-window indices saves only \(O(n^{7/4}(\ln n)^3)\) from that ceiling. The order barrier for \(\mathcal A_n\) is unchanged.

The exact remaining inequality, for each fixed integer \(k\ge 8\) and each fixed \(B>U_k\), is
\[
\mathcal A_n=o(n^2).
\tag{R}
\]
Equivalently, with \(s_n=\lfloor\mathbb E[T]-\lceil n^{1/2}(\ln n)^2\rceil\rfloor\),
\[
\sum_{j\le s_n}
\mathbb E\Bigl[
\operatorname{Cov}\bigl(
\mathbb E[D_d-D_c\mid\mathcal G],\,
\mathbb E[T_0\mid\mathcal G]
\bigr)^2
\Bigr]
=o(n^2).
\]
The covariance is the \(Y\)-covariance in the two-copy resampling space of clause \(j\), and \(\mathcal G\) contains the prefix before \(j\), the two copies, and the shared clauses from \(j+1\) through \(s_n\).

## 12. Conditional bridge, not a theorem

Major’s notes, pages 2–3, give a triangular-array martingale CLT. The row must be a martingale-difference sequence relative to a filtration, the sum of conditional variances must converge to 1 in probability (his (1.2)), and the conditional Lindeberg sum must converge to 0 in probability (his (1.3)). Both conditions are required. Convergence of conditional variances is not implied by convergence of unconditional variances.

If (R) holds, Theorem B gives \(Q/\sigma^2\to 1\) in probability, which is (1.2) for the row \(M_i/\sigma\). I347 already proved that the conditional Lindeberg sum for this row tends to 0 in \(L^1\), hence in probability, for every fixed \(k\ge 4\). Major’s theorem would then yield \((T-\mu)/\sigma\Rightarrow N(0,1)\). The pinned late-cap estimate \(\mathbb E[(H-T)^p]=O((2q^B)^n)\), recorded in I347 Section 2, would transfer the limit from \(T\) to \(H\) and replace \(\sigma^2\) by \(\operatorname{Var}(H)\), which is also \(\Theta(n)\) for \(k\ge 4\). That chain is conditional on (R). It is not proved. No unconditional or conditional CLT is claimed.

Chatterjee’s resampling bound is not re-read in this campaign. I347’s literature note already records that the cubic term is paid by the third-moment bound and that the conditional kernel variance is an equivalent unpaid estimate. Theorem B does not remove that kernel.

## 13. Where the same split stops being little-o

The decomposition \(\kappa=\alpha+\beta\) is valid for every \(k\ge 5\). The estimates do not put the non-\(\alpha\) terms below order \(n^2\) when \(5\le k\le 7\).

- At \(k=7\), \(r=6\) and \(\theta=1/3\). Then \(t^2\mathbb P^\theta\le C n\) throughout the far region, and summing \(\Theta(n)\) indices produces an \(O(n^2)\) majorant for \(\mathbb E|S|^4\). After multiplication by \(n\) and a square root, the post-window contribution to \(R_n\) is \(O(n^2)\), not \(o(n^2)\).
- At \(k=6\), \(r=5\). The same majorant for \(\mathbb E|S|^4\) is \(O(n^{5/2})\), and \(n(\mathbb E|S|^4)^{1/2}\) has order \(n^{9/4}\).
- At \(k=5\), \(r=4\) and \(\theta=0\). Hölder supplies no probability factor. Counting pairs of increments gives an \(O(n^3)\) majorant for \(\mathbb E|S|^4\).
- At \(k=4\), \(r=3\). There is no uniform fourth duration moment, so (6.3) is not known to differ from (6.2) by an \(O(n)\) sum, and Lemma 6 is not available. Theorem A still holds, because it uses only the third moment.

The far-index sum in Lemma 8 is \(o(n^2)\) for every fixed \(k\ge 6\) by the same Hölder argument, and the in-window sum is \(O(n^{3/2}(\ln n)^2)\) for every fixed \(k\ge 5\). Those two savings do not reach (R) while the post-window fourth moment remains of boundary order. No reduction to \(\mathcal A_n\) is claimed for \(4\le k\le 7\).

For \(4\le k\le 7\), the bounded-kernel target (G2) of I347 remains a sufficient route to \(Q/\sigma^2\to 1\) in probability and is not proved here.

## 14. Overlap

R022 is sharp small-information stability for a function \(u:\{-1,1\}^n\to[-1,1]\): the statements (S) and (P) in `frontier/findings/R022-sharp-small-information-stability.md`. The sample space is the discrete cube with bit noise. It contains no random formula and no hitting time. It does not imply (R), (6.2), or a SAT central limit theorem.

Wilson’s quantile separation and Carenini’s window bounds are discussed in the pinned introduction as inputs to the variance theorem and as coarser window technology. Neither is used as a lemma above. A bystander decomposition is not promoted to a Gaussian limit. The pinned upper bound \(O(n)\) already matches Wilson’s \(\Omega(n)\) variance scale; shape is a separate question, and it is the question left open by (R).
