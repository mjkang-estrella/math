# Unequal-entropy EPnI equality: a photon-rate obstruction

Author: Myeongjin Kang. No affiliation. Research date: 2026-10-15.
Original prose: CC BY 4.0. Original checking code: MIT. Copies of other
authors' work retain their original rights; see `RIGHTS.md`.

**Disposition: UNRESOLVED.** Target T is unchanged. The new statement
proved here is a necessary photon-rate comparison at every equality
case. It is saturated by the full Gaussian extremal family, including
unequal entropy and a pure input. It does not force the inputs to be
Gaussian. The campaign count remains **4/10**. No shared file, count,
stage, commit, upload, or subagent was created or changed. This report
is not an independent review and not a Lean certificate.

Round 1 remains immutable at
`frontier/campaigns/2026-10-14/fresh-operator-discovery-r1/`.
Its `candidate.md` has SHA-256
`8c227f21c39e205f8cf95d58f03d82bb06ed7a4e63cdbbe04336d82a8b88353d`.
The copy under `inputs/round1/` matches that digest. Round 1 left the
Gaussian classification complete and left the unequal-entropy
Gaussianity implication unpaid. This round attacks that implication
and stops at a precise analytic gap.

## 1. Fixed target

Let \(n\ge 1\) be finite. Entropies and logarithms are natural. Write

\[
 g(r)=(r+1)\log(r+1)-r\log r,\qquad
 h(r)=g'(r)=\log\bigl(1+1/r\bigr)\quad(r>0),
\]

with \(g(0)=0\) and \(0\log 0=0\). For a finite-energy \(n\)-mode state
put \(r(\rho)=g^{-1}(S(\rho)/n)\). Let \(0<\eta<1\), and let
\(\rho_A,\rho_B\) be independent finite-energy \(n\)-mode states.
Internal entanglement inside either port is unrestricted. Retain

\[
 c_j=\sqrt\eta\, a_j+\sqrt{1-\eta}\, b_j
\]

and write \(\rho_C\) for that reduced state. Set \(a=r(\rho_A)\),
\(b=r(\rho_B)\), and \(c=\eta a+(1-\eta)b\).

Quadrature covariances use
\(V_{jk}=\frac12\operatorname{Tr}\rho\{R_j-d_j,R_k-d_k\}\),
\([R_j,R_k]=i J_{jk}\), and vacuum covariance \(I/2\). A Gaussian state
is a state with Gaussian Weyl characteristic function. Displacements
are arbitrary finite vectors.

**Target T.** Equality \(S(\rho_C)=ng(c)\) holds if and only if both
inputs are Gaussian and either

1. \(a=b\) and \(V_A=V_B\), with no restriction on the common symplectic
   spectrum, or
2. \(a\neq b\) and \(V_A=(a+\tfrac12)SS^T\),
   \(V_B=(b+\tfrac12)SS^T\) for one real symplectic \(S\).

The target includes \(a=0\) or \(b=0\). It assumes no faithfulness,
product-mode, Schwartz, or higher-moment condition. Nothing is claimed
at \(\eta\in\{0,1\}\).

Sufficiency is the Gaussian calculation already recorded in round 1:
in case 2, \(V_C=(c+\tfrac12)SS^T\); in case 1 the three covariances
agree. Displacements do not change entropy. This round does not reopen
that direction.

**Inherited boundaries, not re-proved here.**

- **Proposition G** (round 1, technical): among finite-energy Gaussian
  inputs, equality holds exactly on Target T. The operations are
  Hiroshima's symplectic weak supermajorization, strict convexity of
  the scalar map \(f\) below, and strictness in the determinant
  Minkowski inequality. Round 1 is the source of that argument.
- **Equal entropy.** When \(a=b\), Target T is equality in the linear
  quantum entropy-power inequality. Round 1 credits Li,
  arXiv:2609.40061v1, Theorem 1, for the full finite-energy
  classification in that case. This round does not re-audit that proof.
- **NG, still unpaid.** Every independent finite-energy pair with
  \(S(\rho_A)\neq S(\rho_B)\) and \(S(\rho_C)=ng(c)\) is a pair of
  Gaussian states. The pure-input boundary is included. I117, the
  fixed-thermal-bath uniqueness statement, is a different theorem and
  is not reused as a proof of NG.

The pinned inequality used as a premise is Theorem `thm:epni` of
`The-entropy-photon-number-inequality-September-24-2026` at
`openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`: for independent
finite-energy inputs and \(0\le\eta\le 1\),

\[
 r(\rho_C)\ge \eta\, r(\rho_A)+(1-\eta)\, r(\rho_B).
\]

Its thermal-attenuator corollary asserts attainment and does not assert
uniqueness. Finite energy implies \(0\le S(\rho)\le ng(E/n)\) and
trace-norm compactness of sublevel sets, by the pinned
energy-compactness lemma. Those two statements are the only pinned
facts used in the new proof.

## 2. Round-1 obstructions retained

The following seven facts are kept as stated in round 1. None of them
is a counterexample to Target T. This round's argument does not call the
conditional functional nonnegative, does not send a penalty to zero,
and does not treat finite moments as finite scores.

For fixed unequal levels the scalar function

\[
 f(x,y)=g\bigl(\eta g^{-1}(x)+(1-\eta)g^{-1}(y)\bigr)
\]

is convex and strictly convex off the diagonal. Its support plane at
\((g(a),g(b))\) has coefficients

\[
 p=\frac{\eta h(c)}{h(a)},\qquad
 q_0=\frac{(1-\eta)h(c)}{h(b)},\qquad
 \kappa=g(c)-pg(a)-q_0 g(b),
\]

with the continuous value \(1/h(0)=0\). Round 1 records \(p+q_0<1\) and
\(\kappa<0\). The independent-input functional

\[
 \mathcal D=S(C)-p S(A)-q_0 S(B)-n\kappa
\]

is nonnegative and vanishes exactly on the EPnI equality pairs with
those input entropies. Knowing that the minimum is zero does not
classify the minimizers.

1. **Support plane.** Vanishing of \(\mathcal D\) is exactly the
   entropy-vector form of equality. It is not a Gaussianity proof.
2. **Conditional sign.** Under \(I(A;B\mid M)=0\), \(\mathcal D\)
   conditioned on memory can be negative. Purified thermals at a large
   finite level \(R\), with both purifiers kept as memory, give the
   value \(-n(1-p-q_0)g(R)-n\kappa<0\).
3. **Doubling sign.** Pair a common-squeeze extremizer at levels
   \(a,b\) with an auxiliary thermal pair at the same levels. The sum
   of the two \(\mathcal D\) values is zero, while the balanced
   plus-port is a Gaussian equality case at strictly higher levels
   \(a_t=t(a+\tfrac12)-\tfrac12\) and
   \(b_t=t(b+\tfrac12)-\tfrac12\), \(t=(s+s^{-1})/2>1\), and therefore
   has positive \(\mathcal D\) against the original plane. The chain
   identity forces a negative conditional remainder. The conditional
   linear qEPI is not available, because its coefficients sum to one.
   Choosing the auxiliary squeeze to match an unknown \(S\) is part of
   NG.
4. **Output correlation.** For unequal thermals that attain equality,
   \(I(C;E)=n\{g(c)+g((1-\eta)a+\eta b)-g(a)-g(b)\}>0\) by strict
   concavity of \(g\). Product-output Darmois–Skitovich does not apply.
5. **Penalty removal.** The pinned interpolation argument is proved at
   faithful Gibbs minimizers of a functional that replaces the output
   by a thermal state and adds relative-entropy, energy, and
   fourth-moment penalties. An arbitrary equality state is not known
   to lie in that domain. Sending the penalties to zero does not
   transport a named minimizer. Squeezed equality states are genuine
   and have nonzero defects against the unsqueezed thermal reference,
   so a correct saturation statement has to allow one common quadratic
   shape.
6. **Moments and scores.** The round-1 number-diagonal state with
   weights \(x_k=2^{-k-1}\) and \(y_k=2^{-4^{k+1}}\) is faithful,
   centered, and has every number moment, while the thermal-metric
   dual contributions at reference level 1 are unbounded below by
   \(Z^{-1}(2k+1)2^{k-1}\). Finite moments do not give a finite score.
   That state is not an equality counterexample.
7. **Mutual-information penalty.** No finite \(L\) makes
   \(S(C)-pS(A)-q_0S(B)+L I(A;B)\ge n\kappa\) for every finite-energy
   joint input. The gauge-invariant Gaussian with diagonal blocks
   \((a+\tfrac12)I\), \((b+\tfrac12)I\) and cross-block \(t I\) has
   fixed marginals, mutual information of order \(t^2\), and output
   entropy moving linearly in \(t\) for small negative \(t\).

## 3. Photon-rate domination

Let \(\gamma\) be a real symmetric positive-definite \(2n\times 2n\)
matrix, written in the quadrature basis that the beam splitter mixes
mode by mode. For \(t\ge 0\) let \(N_\gamma(t)\) be the Gaussian
displacement channel of covariance \(t\gamma\): if \(X\) is the
centered classical Gaussian of covariance \(t\gamma\), then

\[
 N_\gamma(t)\rho=\int D(x)\,\rho\, D(x)^\dagger\, dP_X(x),
\]

and \(N_\gamma(0)\) is the identity. Independent increments give the
semigroup \(N_\gamma(s)\circ N_\gamma(t)=N_\gamma(s+t)\). In the
covariance convention above, the channel adds \(t\gamma\) to \(V\) and
adds \(\tfrac t2\operatorname{Tr}\gamma\) to the mean photon number.
Finite energy is preserved.

Write \(\rho(t)=N_\gamma(t)\rho\) and \(\nu(t)=r(\rho(t))\). When the
right derivative exists in the extended interval \([0,\infty]\), write

\[
 \kappa_\gamma(\rho)=\frac{d}{dt}\Big|_{0+}\nu(t).
\]

**Theorem R.** Assume \(S(\rho_C)=ng(c)\). Then, for every such
\(\gamma\),

\[
 \liminf_{t\downarrow 0}\frac{\nu_C(t)-\nu_C(0)}{t}
 \ge
 \limsup_{t\downarrow 0}\frac{\nu_A(t)-\nu_A(0)}{t},
\]

and the same comparison holds with \(B\) in place of \(A\). If
\(S(\rho_A)>0\), then \(\kappa_\gamma(\rho_A)\) and
\(\kappa_\gamma(\rho_C)\) exist in \([0,\infty]\) and
\(\kappa_\gamma(\rho_C)\ge\kappa_\gamma(\rho_A)\). The same holds for
\(B\). Thus, when both input entropies are positive,

\[
 \kappa_\gamma(\rho_C)\ge\max\bigl(\kappa_\gamma(\rho_A),\kappa_\gamma(\rho_B)\bigr).
\]

On every Gaussian pair in Target T, and for every positive-definite
\(\gamma\), the three ports share one rate in \([0,\infty]\). The
common value is finite when every symplectic eigenvalue is strictly
larger than \(1/2\). It is also finite for every pure Gaussian,
including \(a=0\) or \(b=0\). If \(G=SS^T\) in case 2, the common
value at \(\gamma=G\) is \(1\). A product of a vacuum mode and a
positive-entropy thermal mode has infinite isotropic rate: the vacuum
factor contributes \(g(t)\) under \(N_I(t)\), whose derivative at 0
is infinite, while the joint entropy photon number stays positive.
The three ports still agree. This report does not classify the rate
for every mixed vacuum factor and every noise shape.

The inequality is a necessary condition at equality. Section 5 records
why it does not yield NG. Section 4 shows that every known extremizer
saturates it, so the condition does not accidentally exclude the
family the target demands.

### 3.1 Compatibility

Let \(x\) and \(y\) be independent centered Gaussians of covariances
\(s\gamma\) and \(u\gamma\). The beam splitter acts on quadratures by
the same coefficients as on the annihilation operators. The output
displacement on the retained port is
\(z=\sqrt\eta\, x+\sqrt{1-\eta}\, y\), with covariance
\((\eta s+(1-\eta)u)\gamma\). The environment port receives some
displacement \(w=w(x,y)\). For each fixed \((z,w)\), conjugating the
joint output state by \(D_C(z)D_E(w)\) and tracing out \(E\) returns
\(D_C(z)\rho_C D_C(z)^\dagger\), because a unitary on \(E\) alone does
not change the partial trace. Averaging over \((x,y)\) therefore gives

\[
 \operatorname{BS}\circ\bigl(N_\gamma(s)\otimes N_\gamma(u)\bigr)
 (\rho_A\otimes\rho_B)
 =N_\gamma\bigl(\eta s+(1-\eta)u\bigr)(\rho_C).
\]

The identity uses one and the same \(\gamma\) on both ports. It uses
independence of the inputs so that the displacements may be drawn
independently. It does not require the output ports \(C\) and \(E\) to
be independent.

### 3.2 Quotient comparison

The noised inputs \(N_\gamma(s)\rho_A\) and \(\rho_B\) are independent
and of finite energy. The pinned inequality gives, for every \(s>0\),

\[
 \nu_C(\eta s)\ge \eta\,\nu_A(s)+(1-\eta)\, b.
\]

Equality at time zero says \(\nu_C(0)=\eta a+(1-\eta)b\), so

\[
 \frac{\nu_C(\eta s)-\nu_C(0)}{\eta s}
 \ge
 \frac{\nu_A(s)-a}{s}.
\]

The left side is the difference quotient of \(\nu_C\) at time \(\eta s\).
Sending \(s\downarrow 0\) yields the liminf/limsup comparison. The
argument with the roles of the ports exchanged, using noise only on
\(B\), gives the \(B\) bound.

The same comparison with both ports noised is weaker. For speeds
\(\alpha,\beta\ge 0\) and \(t>0\),

\begin{align*}
 &\nu_C\bigl((\eta\alpha+(1-\eta)\beta)t\bigr)\\
 &\qquad\ge
 \eta\,\nu_A(\alpha t)+(1-\eta)\,\nu_B(\beta t).
\end{align*}

Whenever the three derivatives exist and are finite, dividing by \(t\)
and sending \(t\downarrow 0\) yields

\[
 \kappa_\gamma(C)\,(\eta\alpha+(1-\eta)\beta)
 \ge
 \eta\alpha\,\kappa_\gamma(A)+(1-\eta)\beta\,\kappa_\gamma(B)
\]

for every \(\alpha,\beta\ge 0\). The extreme speeds \((\alpha,\beta)=(1,0)\)
and \((0,1)\) are exactly \(\kappa(C)\ge\kappa(A)\) and
\(\kappa(C)\ge\kappa(B)\). Every other speed is a positive combination
of those two inequalities. Varying the speeds does not force
\(\kappa(A)=\kappa(B)=\kappa(C)\).

### 3.3 The entropy is concave along \(N_\gamma\)

For a finite-energy state \(\rho\), define
\(\varphi(t)=S(N_\gamma(t)\rho)\) and
\(\Delta_\rho(t)=\varphi(t)-S(\rho)\). Finite energy bounds the entropy,
so \(\varphi(t)\) is finite.

Each displacement is unitary, so the conditional entropy of the
displaced state given the classical displacement equals \(S(\rho)\).
The mutual information of the classical-quantum state is therefore

\[
 \Delta_\rho(t)=S(N_\gamma(t)\rho)-S(\rho)\ge 0.
\]

This is the integral de Bruijn identity in De Palma–Trevisan,
arXiv:1706.00440v2, Theorem 3.1, and the proof at lines 275–281 of the
frozen text view uses only unitarity of the displacements. The same
lines apply with covariance \(t\gamma\) in place of \(t I\).

The semigroup gives

\[
 \Delta_\rho(s+t)=\Delta_\rho(s)+\Delta_{N_\gamma(s)\rho}(t).
\]

Data processing of mutual information under \(N_\gamma(s)\), which
commutes with displacements, gives
\(\Delta_{N_\gamma(s)\rho}(t)\le\Delta_\rho(t)\). That is Lemma 5 of
the same section, again with unchanged algebra for a fixed \(\gamma\).
The midpoint reduction in their Theorem 3.2, lines 359–382, is purely
algebraic and yields concavity of \(\Delta_\rho\), hence of \(\varphi\),
once continuity is known.

Continuity at \(t=0\) is proved from the pinned compactness lemma
rather than from their thermal-reference estimate. Normalized
photon-number truncations \(\rho_K\) converge to \(\rho\) in trace
norm and have finite rank. On a finite-rank state the Weyl operators
are strongly continuous, so
\(x\mapsto D(x)\rho_K D(x)^\dagger\) is continuous in trace norm. The
Gaussian measures of covariance \(t\gamma\) converge weakly to a point
mass at the origin, and the integrand is bounded by 2, so
\(\|N_\gamma(t)\rho_K-\rho_K\|_1\to 0\). The channel contraction then
gives

\[
 \|N_\gamma(t)\rho-\rho\|_1
 \le 2\|\rho-\rho_K\|_1+\|N_\gamma(t)\rho_K-\rho_K\|_1.
\]

Thus \(N_\gamma(t)\rho\to\rho\) in trace norm. For \(t\in[0,1]\) the
mean photon numbers are at most
\(E+\tfrac12\operatorname{Tr}\gamma\). The pinned lemma says entropy
is continuous on that energy set. Therefore \(\varphi(t)\to\varphi(0)\).
Applying the same fact to \(N_\gamma(t_0)\rho\), which still has finite
energy, gives continuity at every \(t_0\ge 0\). Monotonicity is
\(\Delta\ge 0\).

A continuous concave function on \([0,\infty)\) has nonincreasing
difference quotients: if \(0<s<t\), concavity on the segment from 0
to \(t\) gives
\((\varphi(s)-\varphi(0))/s\ge(\varphi(t)-\varphi(0))/t\). The right
derivative \(\varphi'(0)\) therefore exists in \([0,\infty]\).

### 3.4 From the entropy derivative to \(\kappa\)

Suppose \(S(\rho)>0\). Then \(\nu(0)>0\) and \(h(\nu(0))\) is finite and
positive. The inverse \(g^{-1}\) is \(C^1\) on \((0,\infty)\), with
derivative \(1/h\). For each small \(t>0\) the mean-value theorem
supplies a point \(\xi_t\) between \(S(\rho)/n\) and \(S(\rho(t))/n\)
such that

\[
 \frac{\nu(t)-\nu(0)}{t}
 =\frac{1}{h(\xi_t)}\cdot\frac{S(\rho(t))-S(\rho)}{nt}.
\]

As \(t\downarrow 0\), one has \(\xi_t\to\nu(0)\) and the entropy
quotient tends to \(\varphi'(0)\). Hence \(\kappa_\gamma(\rho)\) exists
in \([0,\infty]\) and equals \(\varphi'(0)/(n h(\nu(0)))\), with the
value \(+\infty\) when the entropy derivative is infinite.

Theorem R's comparison of derivatives, for positive input entropy, is
the quotient comparison of Section 3.2 together with this existence.
At zero entropy the chain rule is not claimed: \(h(r)\to\infty\) as
\(r\downarrow 0\), and a finite photon-rate can sit under an infinite
entropy derivative. The vacuum examples in Section 4 are computed
directly. The liminf form in Theorem R covers the zero-entropy case
without a chain rule.

## 4. Saturation on the extremal family

### 4.1 Shape-matched noise

Let \(G=SS^T\) with \(S\) symplectic, and let \(u\ge\tfrac12\). The
Gaussian of covariance \(u G\) has every symplectic eigenvalue equal
to \(u\), because \(u G=S(u I)S^T\) and conjugation by a symplectic
matrix preserves symplectic eigenvalues. Its entropy photon number is
\(u-\tfrac12\).

Adding \(t G\) produces covariance \((u+t)G\), with entropy photon
number \(u+t-\tfrac12\). The derivative in \(t\) is \(1\), at every
\(u\ge\tfrac12\) and for every \(t\ge 0\). In case 2 of Target T the
three covariances are \(u_A G\), \(u_B G\), and \(u_C G\) with
\(u_C=\eta u_A+(1-\eta)u_B\). All three photon rates at \(\gamma=G\)
equal 1, including when \(u_A=\tfrac12\) or \(u_B=\tfrac12\).

### 4.2 Arbitrary noise

Keep \(G=SS^T\) and let \(\gamma\) be an arbitrary positive-definite
matrix. Symplectic eigenvalues of \(u G+t\gamma\) equal those of

\[
 u I+t\gamma',\qquad
 \gamma'=S^{-1}\gamma(S^{-1})^T,
\]

since \(u G+t\gamma=S(u I+t\gamma')S^T\). If \(\lambda_j(\varepsilon)\)
are the symplectic eigenvalues of \(I+\varepsilon\gamma'\), then the
symplectic eigenvalues of \(u I+t\gamma'\) are \(u\lambda_j(t/u)\).
At \(\varepsilon=0\) every \(\lambda_j\) equals 1. The sum
\(\Lambda(\varepsilon)=\sum_j\lambda_j(\varepsilon)\) is differentiable
at 0: the Hermitian matrix \(i J(I+\varepsilon\gamma')\) has its
positive and negative eigenvalues separated by a gap near \(\pm 1\) for
small \(\varepsilon\), so the sum of the positive cluster is a
contour integral of the resolvent and is smooth in \(\varepsilon\).

Scaling gives

\[
 \sum_j\mu_j(u,t)=u\,\Lambda(t/u),
 \qquad
 \frac{d}{dt}\Big|_{0}\sum_j\mu_j=\Lambda'(0),
\]

which does not depend on \(u\). For \(u>1/2\) every thermal parameter
starts at the same positive value \(\rho=u-1/2\). The function
\(g(\,\cdot\,-1/2)\) is analytic in a neighborhood of \(u\), and the
sum of its values on the positive symplectic cluster is a contour
integral of the resolvent, hence differentiable. Its derivative at
\(t=0\) equals \(h(\rho)\) times \(\Lambda'(0)\). Dividing by
\(n h(\rho)\) shows that the entropy-photon derivative equals the
finite number \(\kappa_*=\Lambda'(0)/n\), independent of \(u>1/2\).

For the pure case \(u=1/2\), the same scaling gives
\(\sum_j(\mu_j(t)-1/2)=n\kappa_* t+o(t)\). Let
\(\nu_j(t)=\mu_j(t)-1/2\) and let \(r(t)\) be the entropy photon
number, so \(g(r)=(1/n)\sum_j g(\nu_j)\). Concavity of \(g\) yields
\(r(t)\le (1/n)\sum_j\nu_j\), hence \(\limsup_{t\downarrow 0} r(t)/t\le\kappa_*\).
For the matching lower bound, concavity and \(g(0)=0\) give
\(g(x)\ge\frac{x}{x+y}g(x+y)\) and the symmetric bound in \(y\), so
\(g\) is subadditive and \(\sum_j g(\nu_j)\ge g(\sum_j\nu_j)\). Thus
\(g(r)\ge g(\sigma)/n\) with \(\sigma=\sum_j\nu_j\). For
\(0<x\le 1/2\),

\[
 x\log(1/x)\le g(x)\le x\log(1/x)+2x.
\]

If \(\kappa_*=0\), the upper bound forces \(r(t)=o(t)\). If
\(\kappa_*>0\), then \(\sigma\sim n\kappa_* t\), and for small \(t\)
both \(\sigma\) and \(r(t)\) lie in \((0,1/2]\). Subadditivity and the
lower estimate on \(g\) give
\(g(r)\ge(\sigma/n)\log(1/\sigma)\). Suppose a sequence has
\(r(t)/t\to L\). The bound \(r\le\sigma/n\) forces \(L\le\kappa_*\).
Along that sequence \(r=\varepsilon t\) with \(\varepsilon\to L\), so

\[
 \frac{r\log(1/r)+2r}{t\log(1/t)}
 =\varepsilon\cdot\frac{\log(1/t)-\log\varepsilon}{\log(1/t)}
  +\frac{2\varepsilon}{\log(1/t)}
\]

tends to \(L\), including when \(L=0\) and \(-\varepsilon\log\varepsilon\to 0\).
The comparison quantity \((\sigma/n)\log(1/\sigma)\) divided by
\(t\log(1/t)\) tends to \(\kappa_*\). If \(L<\kappa_*\), then
\(g(r)\le r\log(1/r)+2r\) is eventually smaller than
\(g(\sigma)/n\), a contradiction. Hence \(L=\kappa_*\) and
\(r(t)/t\to\kappa_*\). The pure Gaussian has the same finite photon
rate as every positive level on the same ray \(u G\).

Consequently every case-2 triple, including a zero on either port,
shares one finite value of \(\kappa_\gamma\).

In case 1 the three Gaussian states have the same covariance, up to
displacement. A displacement commutes with \(N_\gamma\) and does not
change entropy, so the three rates agree whenever either rate exists.
When every symplectic eigenvalue exceeds \(1/2\), the contour
argument used above shows that the common rate exists and is finite:
\(g(\,\cdot\,-1/2)\) is analytic near each initial symplectic
eigenvalue, and the entropy derivative equals that analytic spectral
derivative. Those spectra occur in the equality class only when
\(a=b\), which is Proposition G, not a new constraint. The infinite
isotropic example in the statement of Theorem R is the product case
already named there; existence for a general mixed vacuum factor is
not needed for case 2 and is not claimed for every \(\gamma\).

### 4.3 One-mode isotropic formula

For a one-mode Gaussian, \(\nu=\sqrt{\det V}-\tfrac12\). Differentiating
\(\det(V+t\gamma)\) gives

\[
 \kappa_\gamma=\frac{\sqrt{\det V}}{2}\operatorname{Tr}(V^{-1}\gamma).
\]

If \(V=u G\) with \(\det G=1\), this equals
\(\tfrac12\operatorname{Tr}(G^{-1}\gamma)\), which is independent of
\(u\) and equals 1 at \(\gamma=G\). For \(\gamma=I\) and
\(G=\operatorname{diag}(s^2,s^{-2})\),

\[
 \kappa_I=\varphi:=\frac{s^2+s^{-2}}{2}\ge 1.
\]

The same value is attached to every photon level with that squeeze.
Unequal-entropy extremizers therefore satisfy
\(\kappa_I(A)=\kappa_I(B)=\kappa_I(C)=\varphi\), which may be strictly
larger than 1.

## 5. Why the rate bound does not give NG

### 5.1 The convex combination is false

The estimate that would upgrade Theorem R to rate coincidence is

\[
 \kappa_\gamma(C)\le\eta\,\kappa_\gamma(A)+(1-\eta)\,\kappa_\gamma(B)
\]

for every independent pair and every positive-definite \(\gamma\).
Together with Theorem R it would force
\(\kappa(A)=\kappa(B)=\kappa(C)\) at every positive-entropy equality
case. That estimate is false for one-mode Gaussians.

Take \(\eta=\tfrac12\), \(V_A=\operatorname{diag}(5,1)\), and
\(V_B=\operatorname{diag}(1,\tfrac35)\). Independence gives
\(V_C=\operatorname{diag}(3,\tfrac45)\). The determinants are
\(5\), \(\tfrac35\), and \(\tfrac{12}{5}\), each strictly larger than
\(\tfrac14\), so all three matrices are physical covariances. The
isotropic rates are

\begin{align*}
 \kappa(A)&=\frac{3}{\sqrt 5},&
 \kappa(B)&=\frac{4\sqrt{15}}{15},&
 \kappa(C)&=\frac{19\sqrt{15}}{60}.
\end{align*}

Their comparison simplifies by rational arithmetic to

\[
 \kappa(C)-\frac{\kappa(A)+\kappa(B)}{2}
 =\frac{\sqrt 5}{60}\bigl(11\sqrt 3-18\bigr).
\]

The factor in parentheses is positive because
\(11^2\cdot 3=363>324=18^2\). The same pair is a strict EPnI
inequality. The entropy-photon excess is

\[
 \nu(C)-\bar c=\frac{\sqrt 5}{10}\bigl(3\sqrt 3-5\bigr),
\]

and \(3\sqrt 3>5\) because \(27>25\). A differentiation of this false
universal bound cannot be the missing step. On the known extremal
family the two sides agree, by Section 4, so the family itself does
not contain a counterexample. Restricting the false bound to the
equality set by fiat would assume the rate coincidence one is trying
to prove.

### 5.2 One-mode isotropic rates are quasiconvex, and that is still short

For a positive-definite \(2\times 2\) matrix let
\(\rho=\lambda_{\max}/\lambda_{\min}\ge 1\) and

\[
 \kappa(V)=\frac{\sqrt\rho+1/\sqrt\rho}{2}.
\]

This is the isotropic formula of Section 4.3. The sublevel
\(\{\kappa\le\varphi\}\) is the set of matrices whose eigenvalue ratio
is at most the corresponding \(\rho_\varphi\). That set equals

\[
 \bigcup_{t>0}\{V:t I\le V\le \rho_\varphi\, t I\}.
\]

It is convex: if \(t I\le A\le\rho t I\) and \(s I\le B\le\rho s I\),
the convex combination lies between
\((\eta t+(1-\eta)s)I\) and \(\rho_\varphi\) times that multiple of
\(I\). Consequently, for one-mode covariances and isotropic noise,

\[
 \kappa(V_C)\le\max\bigl(\kappa(V_A),\kappa(V_B)\bigr).
\]

The uncertainty relation is not used. Combined with Theorem R, every
one-mode Gaussian equality case satisfies
\(\kappa_I(C)=\max(\kappa_I(A),\kappa_I(B))\). Proposition G already
gives the stronger conclusion that the covariances are proportional,
which forces the three isotropic rates to be equal, not merely ordered
by a maximum. The quasiconvex bound does not see non-Gaussian states.
An ordered maximum still permits one input rate to be strictly smaller
than the output rate. It does not force the common symplectic shape.

The bound is sharp enough to show that a maximum, rather than a convex
combination, is the right universal comparison for this particular
rate. Opposite one-mode squeezes
\(V_A=\operatorname{diag}(4,1)\) and \(V_B=\operatorname{diag}(1,4)\)
have isotropic rate \(\tfrac54\), while their average
\(V_C=\operatorname{diag}(\tfrac52,\tfrac52)\) has rate \(1\). Here
\(\nu(C)=2\) and the EPnI threshold is \(\tfrac32\), so the pair is not
an equality case. Theorem R's lower bound is an equality-case
statement: off the equality set the output rate may lie strictly below
both input rates.

### 5.3 Stam saturation excludes the unequal extremizers

For the one-mode geometric law of mean \(r\), the isotropic entropy
production equals \(h(r)\). Indeed
\(p_k=(1-\lambda)\lambda^k\) with \(\lambda=r/(r+1)\) gives
\(\log p_k-\log p_{k+1}=h(r)\) and

\[
 \sum_{k\ge 0}(k+1)(p_k-p_{k+1})h(r)
 =h(r),
\]

because \(\sum_{k\ge 0}(k+1)\lambda^k=1/(1-\lambda)^2\) and
\(p_k-p_{k+1}=(1-\lambda)^2\lambda^k\). A product of \(n\) such modes
has entropy production \(n h(r)\) under the isotropic semigroup, since
the semigroup and the entropy both add over modes. The photon rate is
therefore \(1\).

Let \(w(r)=1/h(r)\) for \(r>0\), and \(w(0)=0\). Differentiating
\(w=1/h\) gives

\[
 w''(r)=\frac{2-(2r+1)h(r)}{r^2(r+1)^2 h(r)^3}.
\]

For \(t=1/(2r+1)\in(0,1]\) one has
\(h(r)=\log((1+t)/(1-t))\). The function
\(\psi(t)=\log(1+t)-\log(1-t)-2t\) satisfies \(\psi(0)=0\) and
\(\psi'(t)=2t^2/(1-t^2)>0\) on \((0,1)\), so \(h(r)>2/(2r+1)\) and
\(w''<0\). Thus \(w(c)>\eta w(a)+(1-\eta)w(b)\) whenever \(a\neq b\).

At an unequal thermal extremizer the Fisher informations are
\(J(A)=h(a)\), \(J(B)=h(b)\), and \(J(C)=h(c)\), up to the mode count
\(n\) which cancels in the ratios. The harmonic comparison encoded by
\(w\) is therefore strict: \(J(C)\) lies strictly below the harmonic
mean of \(J(A)\) and \(J(B)\) that a saturated linear Stam bound would
require. The photon rates are nevertheless all equal to 1. Any
equality analysis that requires saturation of that harmonic Fisher
bound excludes every unequal-entropy thermal extremizer. The same
exclusion hits every common-squeeze extremizer under isotropic noise,
where all three photon rates equal \(\varphi>1\) while the underlying
thermal levels still differ.

This comparison is computed on the explicit Gaussian states. It does
not import a general Stam theorem, and it does not assert that no
corrected Fisher inequality exists. It says that the uncorrected
harmonic saturation condition is the wrong equality case for Target T.

### 5.4 Isotropic noise leaves the equality set

Let both inputs be one-mode Gaussians with the same squeeze \(s>1\),
levels \(a\neq b\), and \(\varphi=(s^2+s^{-2})/2\). Isotropic noise of
duration \(t\) replaces \(u=r+\tfrac12\) by the determinant identity

\[
 \det(V+t I)=u^2+2\varphi u t+t^2.
\]

The entropy photon number is the square root of that determinant,
minus \(\tfrac12\). At \(t=0\) the first derivative is \(\varphi\) and
the second derivative is \((1-\varphi^2)/u\). Along the synchronized
flow, whose output time equals the common input time,

\begin{align*}
 \delta(t)&=\nu_C(t)-\eta\nu_A(t)-(1-\eta)\nu_B(t),\\
 \delta(0)&=0,\\
 \delta'(0)&=\varphi-\eta\varphi-(1-\eta)\varphi=0,\\
 \delta''(0)&=(1-\varphi^2)
 \Bigl(\frac1{u_C}-\frac{\eta}{u_A}-\frac{1-\eta}{u_B}\Bigr).
\end{align*}

Here \(u_C=\eta u_A+(1-\eta)u_B\). The map \(u\mapsto 1/u\) is strictly
convex on \((0,\infty)\), so the bracket is negative when \(a\neq b\).
Also \(1-\varphi^2<0\) when \(s\neq 1\). The product is positive.
Equality is an isolated minimum along this path: for small \(t>0\) the
noised pair is a strict EPnI inequality.

The rational case \(s=2\), \(a=\tfrac1{10}\), \(b=1\), \(\eta=\tfrac12\)
has \(\varphi=\tfrac{17}{8}\), \(u_A=\tfrac35\), \(u_B=\tfrac32\),
\(u_C=\tfrac{21}{20}\), and

\[
 \delta''(0)=\frac{675}{896}>0.
\]

Heat flow with a noise shape chosen independently of \(S\) does not
preserve equality. A regularization that replaces an equality pair by
its isotropic evolution, and then passes to the limit, has to account
for a deficit that becomes positive at every positive time. The
shape-matched flow of Section 4.1 does preserve equality, because both
levels increase by the same additive constant and the common \(S\) is
unchanged. Using that flow as a regularization assumes the \(S\) that
NG is supposed to produce.

The large-time expansion does not repair this. For any one-mode
covariance,

\[
 \sqrt{\det(V+t I)}=t+\tfrac12\operatorname{Tr}(V)+O(t^{-1}).
\]

On independent inputs \(\operatorname{Tr} V_C=\eta\operatorname{Tr} V_A+(1-\eta)\operatorname{Tr} V_B\), so the constant terms cancel in \(\delta(t)\) and \(\delta(t)\to 0\) as \(t\to\infty\). This cancellation holds for the opposite-squeeze pair of Section 5.2, which never attains equality, and for the common-squeeze pair, which attains equality only at \(t=0\). The limit of the deficit does not detect equality.

### 5.5 Linearity in the noise shape is not free

On the Gaussian family, Section 4.2 shows that \(\kappa_\gamma\) depends
on \(\gamma\) and on \(G\), and not on the photon level. In one mode
the dependence on \(\gamma\) is linear. For a general finite-energy
state, Section 3.3 gives a derivative for each fixed \(\gamma\),
separately. Additivity
\(\kappa_{\gamma_1+\gamma_2}=\kappa_{\gamma_1}+\kappa_{\gamma_2}\)
would need an interchange between the entropy derivative and a sum of
generators. Finite energy does not provide that interchange.
Round-1 objection 6 is the same domain warning in score language.
Theorem R is therefore a family of scalar inequalities, one for each
\(\gamma\). It is not a Loewner comparison of Fisher matrices.

## 6. The remaining gap

NG is open. No counterexample to Target T is claimed. The proved
necessary condition is compatible with every extremizer the target
names.

The missing analytic step, if it exists inside this rate formalism, is
an upper bound that uses equality in a way Theorem R does not. Two
weaker statements are already identified and are not that step.

- Rate coincidence \(\kappa_\gamma(A)=\kappa_\gamma(B)=\kappa_\gamma(C)\)
  for every \(\gamma\), on an arbitrary equality pair, is not proved.
  The speed comparison cannot produce it. The convex combination would
  produce it and is false outside the equality set.
- Even proved coincidence would still leave a Gaussianity implication.
  The isotropic numerical value is not a classifier: unequal thermals
  have \(\kappa_I=1\), while common squeezes have \(\kappa_I=\varphi>1\)
  and are equally extremal. A theorem that forced \(\kappa_I=1\) would
  delete the squeezed family.

The same gap can be phrased without rates. One needs a saturation
analysis of the pinned interpolation at an unregularized equality
state, allowing a common quadratic shape, or a different extremality
argument that keeps the symplectic family. Section 2, item 5, is still
the obstruction to reading that saturation off the penalized Gibbs
calculation. This round does not supply the missing saturation
statement.

What was ruled out, in addition to the seven round-1 routes, is the
following group of heat-flow shortcuts.

- Synchronized isotropic noise does not stay inside the equality set
  when \(a\neq b\) and the common squeeze is nontrivial.
- The universal convex combination of photon rates is false.
- Harmonic saturation of isotropic Fisher information is false on the
  unequal thermal extremizers, which do saturate the photon-rate
  bound.
- Sending both noise speeds independently produces no constraint beyond
  Theorem R.
- For one-mode Gaussians, the deficit against synchronized isotropic
  noise tends to zero at infinite time whether or not equality holds
  at time zero.

## 7. Source contract

Pinned commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The local
files under `inputs/upstream/epni/` are the section texts named below.
`receipts/fetch.json` records the raw URLs, byte counts, SHA-256, and
Git blob SHA-1. Those five hashes agree with the round-1 upstream
receipt. Sections 03 and 06 were not copied in this round and are not
premises.

Reading extents used as premises or as inherited statements:

| Local file | Extent | Role |
| --- | --- | --- |
| `inputs/upstream/epni/00-introduction.tex` | lines 1–80 | `thm:epni`, thermal-attenuator corollary, attainment without uniqueness |
| `inputs/upstream/epni/01-preliminaries.tex` | lines 1–80 | Gibbs lemma and energy-compactness lemma, including both proofs |
| `inputs/literature/conditional-1706.00440v2.txt` | lines 248–407 | integral de Bruijn identity, concavity reduction, existence of the Fisher derivative for isotropic noise |
| `inputs/literature/depalma-thesis-1710.09395v1.txt` | lines 1358–1487 | Stam form (3.77)–(3.78) and the start of the noise asymptotic; not a premise of Theorem R |
| `inputs/round1/candidate.md` | entire file, 733 lines | Target T, Proposition G, and the seven obstructions |

The derivative existence used in Theorem R is the concavity argument
of De Palma–Trevisan, Theorem 3.2, transferred from covariance \(t I\)
to covariance \(t\gamma\), with continuity re-proved from the pinned
energy lemma and strong continuity of the Weyl representation. The
transfer uses that \(N_\gamma\) is a commutative displacement semigroup.
It does not use their Stam theorem. The thesis passage was read to
check the older heat-flow route and is not cited as a proof of EPnI
equality.

Round 1's readings of Li, Hiroshima, Cuesta, and the remaining EPnI
sections are inherited only at the boundary stated in Section 1.
This round does not claim a new reading of those proofs. Proposition G
is not re-derived. Li's equal-entropy theorem is not re-derived.

Sections `02-interpolation.tex`, `04-metric.tex`, and
`05-stationarity.tex` are present as pinned copies so the fetch can be
checked. They are not premises of Theorem R. Their penalty hypotheses
are exactly the domain obstruction in Section 2, item 5, as round 1
stated them.

No priority claim is made. The rate comparison at equality was not
found, in the pages read this round, as a stated equality-case theorem.
That is a statement about those pages, not a claim that the comparison
is absent from the literature.

## 8. Checks, integrity, and handoff

From this directory:

```bash
python -B checks/check.py
python -B checks/verify_manifest.py
```

`checks/check.py` uses integer and rational arithmetic only. It
certifies:

- \(363>324\), hence the isotropic convex-combination gap of
  \(\operatorname{diag}(5,1)\) and \(\operatorname{diag}(1,3/5)\) is
  positive;
- \(27>25\), hence that pair is a strict EPnI inequality, together with
  the three determinant comparisons against \(1/4\);
- \(\delta''(0)=675/896>0\) and \(\delta'(0)=0\) for the squeezed flow
  \(s=2\), \(a=1/10\), \(b=1\), \(\eta=1/2\);
- the opposite-squeeze rates \(5/4,5/4,1\) and the strict photon excess
  \(2>3/2\);
- exact cancellation of the large-time constant
  \(\varphi u_C-\eta\varphi u_A-(1-\eta)\varphi u_B\).

These identities support the sign claims in Section 5. They are not a
proof of Theorem R and not a proof of NG. Theorem R is the analytic
argument in Section 3.

`inputs-manifest.json` binds the frozen inputs.
`outputs-manifest.json` binds this report, the rights notice, the
checkers, and the receipts, excluding itself. `seal.json` binds the
owned inventory except its own bytes. The verifier recomputes those
hashes and reruns the rational checks. It does not fetch, reseal, or
write a shared index.

No Lean development is included. A later formalization could cover the
one-mode covariance arithmetic and the rational sign checks. It would
not discharge NG, and no axiom encoding NG is proposed.

**Handoff.** Target T is open. The proved addition is Theorem R:
at every EPnI equality, every positive-definite displacement noise
has output photon-rate liminf at least the input photon-rate limsup,
and the resulting derivatives exist and obey the same comparison when
the input entropy is positive. The full Gaussian extremal family
saturates the comparison, with common value 1 for shape-matched noise.
The unpaid statement is still NG. The convex combination that would
turn Theorem R into rate coincidence is false for explicit one-mode
Gaussians, and rate coincidence itself would not yet be Gaussianity.
Count remains 4/10 until a separate acceptance. No independent
proof, contribution, or manuscript review is claimed.
