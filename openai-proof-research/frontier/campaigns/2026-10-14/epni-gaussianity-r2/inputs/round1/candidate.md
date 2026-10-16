# Two-input bosonic entropy equality: an unresolved Gaussianity bridge

Author: Myeongjin Kang. No affiliation. Research date: 2026-10-15.
Original prose: CC BY 4.0. Original checking code: MIT. Copies of other
authors' work retain their original rights; see `RIGHTS.md`.

**Disposition: UNRESOLVED; no substantial complete theorem is nominated.**
The selected target is the full equality classification in the two-input
entropy photon-number inequality (EPnI). I prove the proposed classification
within the Gaussian inputs, reduce the remaining assertion to one exact
Gaussianity implication, and give analytic obstructions to two plausible
proof routes. One obstruction occurs inside the actual doubling circuit,
with a known extremizer and a thermal auxiliary at the correct entropy
levels. The original target is neither proved nor refuted. The supporting
results below are technical deductions, not a replacement nomination.
The campaign remains **4/10**. No shared file, count, stage, commit,
upload, message to another person, or subagent was created or changed.
There has been no independent review of this work and no Lean certificate.

## 1. Bounded selection and contribution boundary

I screened two directions: parameter-dependent spatial rigidity from strong
Kadison--Kastler stability, and equality in bosonic entropy mixing. For the
first, I read the exact pinned strong-stability theorem and the preceding
I82 structural-discovery report. The theorem supplies a small implementing
unitary for each pair of algebras, without a continuously selected unitary
for a parameter family. Turning it into a substantial new result would
require a separate selection/normalizer theorem and an adequate prior-art
comparison. I did not turn pointwise existence into a claimed bundle
theorem, and stopped that screen.

The second direction has a precise unpaid interface. The pinned EPnI paper
proves the inequality for arbitrary finite-energy input states, including
internal multimode entanglement, and thermal attainment. It explicitly does
not assert uniqueness in its thermal-attenuator corollary. Li's primary
paper proves equality for the **linear and exponential qEPI**, not EPnI at
unequal entropy levels. The project's I117 already proves fixed-thermal-bath
uniqueness at positive temperatures, and classifies that deduction as
technical. It is not reopened here.

The new target would identify all two-free-port optimizers. It does not ask
for another numerical-range equality witness, an amplification hierarchy,
a binary-information stability estimate, the fixed-bath power rate in I114/
I117, or an adaptive zero-key theorem. R016, R019, R020, R022 and R024 are
not used to manufacture a new count. No Borsuk sources or other active
discovery directories were used.

The prior-art comparison is bounded. Actual readings include De Palma's
thesis Appendix A.8, Hiroshima's symplectic majorization theorem and proof,
Li's equality theorems and doubling proof, Cuesta's exact characterization
and stability statements, the conditional qEPI theorem, and the 2018
Gaussian-optimizer review's EPnI/Young sections. These readings do not
establish worldwide priority. In particular, the scalar convexity and
symplectic comparison used below are **credited older operations**.

## 2. Exact full target

Let \(n\geq1\) be any finite integer. On the \(n\)-mode bosonic Fock space
let \(N=\sum_j a_j^*a_j\), and use natural-log von Neumann entropy. Write

\[
 g(r)=(r+1)\log(r+1)-r\log r,\qquad
 h(r)=g'(r)=\log(1+1/r),\qquad r>0,
\]

with \(g(0)=0\). For any state \(\rho\) of finite mean total photon number,
put \(r(\rho)=g^{-1}(S(\rho)/n)\). Let \(0<\eta<1\), and let
\(\rho_A,\rho_B\) be **independent** input states with
\(\operatorname{Tr}\rho_A N,\operatorname{Tr}\rho_B N<\infty\).
Each state may have arbitrary correlations and entanglement between its
own modes. Retain the output

\[
 c_j=\sqrt\eta\,a_j+\sqrt{1-\eta}\,b_j
\]

and call its state \(\rho_C\). Set \(a=r(\rho_A)\), \(b=r(\rho_B)\), and
\(c=\eta a+(1-\eta)b\).

Quadrature covariances are
\(V_{jk}=\tfrac12\operatorname{Tr}\rho\{R_j-d_j,R_k-d_k\}\), with
\([R_j,R_k]=iJ_{jk}\); the vacuum covariance is \(I/2\).
A Gaussian state is specified by its Gaussian Weyl characteristic function.
Its displacement is unrestricted below.

**Target T.** Equality

\[
 S(\rho_C)=n g(c)                                                   \tag{T}
\]

holds if and only if both inputs are Gaussian and one of the following
conditions holds:

1. \(a=b\) and \(V_A=V_B\), with no restriction on their common symplectic
   spectrum;
2. \(a\ne b\) and there is a real symplectic matrix
   \(S\in\operatorname{Sp}(2n,\mathbb R)\) such that

   \[
     V_A=(a+\tfrac12)SS^T,\qquad V_B=(b+\tfrac12)SS^T.               \tag{G}
   \]

This includes zero input entropy, arbitrary finite energy rather than an
energy cap, all finite mode counts, and all nontrivial transmissivities.
There is no product-mode, faithfulness, Schwartz, or higher-moment
hypothesis. Nothing is claimed at \(\eta=0,1\), where all inputs attain
equality. Common squeezing and mode mixing are part of the claimed
extremal family; they cannot be omitted by calling every optimizer thermal
in the original coordinates.

Sufficiency is immediate from Gaussian covariance mixing. In (G),
\(V_C=(c+1/2)SS^T\), so \(S(C)=ng(c)\). Equal covariance gives equal
input/output Gaussian entropy. Displacements only produce output
displacements and do not change entropy. A common symplectic change on
both ports commutes with the beam-splitter symplectic matrix.

At \(a=b\), (T) is exactly equality in the linear qEPI. Li's Theorem 1
already gives the asserted full finite-energy classification in that
case. Section 4 below completes the Gaussian case at unequal entropies.
Consequently the exact remaining bridge is:

> **NG.** Every independent finite-energy pair attaining (T) with
> \(S(\rho_A)\ne S(\rho_B)\) consists of Gaussian states.

NG is unproved here, including its possible one-pure-input boundary. It is
the original target's missing implication, not an additional hypothesis
under which the full target is announced solved.

## 3. Scalar support geometry, with its older origin made explicit

For fixed \(\eta\), let

\[
 f(x,y)=g\bigl(\eta g^{-1}(x)+(1-\eta)g^{-1}(y)\bigr),\qquad x,y\ge0.
\]

The following calculation is the photon-number normalization of De Palma's
Appendix A.8, equations (A.77)--(A.84), not a new convexity theorem.
I give the calculation to make the exact equality interface explicit.

For \(r>0\), define

\[
 k(r)=r(r+1)h(r),\qquad q(r)=1/k(r).
\]

Then \(k(0)=0\) by continuous extension, and

\[
 k''(r)=2h(r)-\frac{2r+1}{r(r+1)}<0.                               \tag{3.1}
\]

For example, after putting \(t=1/r\), the last inequality follows because
the function
\(t(2+t)/(2(1+t))-\log(1+t)\) vanishes at zero and has derivative
\(t^2/(2(1+t)^2)>0\).

At \(x=g(a),y=g(b)\), with \(a,b>0\), and for real \(\xi,\zeta\), put
\(u=\xi/h(a),v=\zeta/h(b)\). Direct differentiation gives

\[
 D^2f[(\xi,\zeta)]^2
 =h(c)\{\eta q(a)u^2+(1-\eta)q(b)v^2
       -q(c)(\eta u+(1-\eta)v)^2\}.                               \tag{3.2}
\]

Weighted Cauchy--Schwarz bounds the last square by

\[
 [\eta k(a)+(1-\eta)k(b)]
 [\eta q(a)u^2+(1-\eta)q(b)v^2].
\]

Strict concavity in (3.1) proves that the Hessian is positive definite
when \(a\ne b\). At \(a=b\), (3.2) is
\(h(a)q(a)\eta(1-\eta)(u-v)^2\). Thus \(f\) is convex, is strictly
convex along every nonconstant segment not contained in \(x=y\), and
\(f(x,x)=x\). Convexity extends to the closed quadrant by continuity.
On an axis away from the origin the one-variable second derivative is
strictly positive: in (3.2) use
\(k((1-\eta)b)>(1-\eta)k(b)\), or its exchanged version. These facts
also prove the stated strict-segment conclusion for boundary segments.

In particular, equality in finite Jensen averaging at an off-diagonal
barycenter forces all the averaged points to coincide. Indeed, a distinct
point and an off-diagonal point give a segment with strictly positive
curvature on an open part; if all points are on the diagonal then the
barycenter is on the diagonal as well.

For fixed unequal \(a,b\ge0\), define

\[
 p=\frac{\eta h(c)}{h(a)},\qquad
 q_0=\frac{(1-\eta)h(c)}{h(b)},\qquad
 \kappa=g(c)-p g(a)-q_0g(b),                                      \tag{3.3}
\]

where \(1/h(0)=0\). The subscript on \(q_0\) distinguishes the scalar
coefficient from \(q(r)\) in (3.2). The supporting-plane inequality is

\[
 f(x,y)\ge p x+q_0y+\kappa,                                      \tag{3.4}
\]

with equality only at \((x,y)=(g(a),g(b))\). This also holds at a
one-axis reference: the derivative of \(g^{-1}\) at zero is zero, so
the corresponding component of the supporting gradient is zero, and
the strict-segment argument applies.

Two further strict signs will be useful. Put \(w(r)=1/h(r)\), with
\(w(0)=0\). Then

\[
 w''(r)=\frac{2-(2r+1)h(r)}{r^2(r+1)^2h(r)^3}<0,                  \tag{3.5}
\]

because, for \(t=1/(2r+1)\),
\(h(r)=2\operatorname{artanh}(t)>2t\). Therefore

\[
 d:=1-p-q_0>0,\qquad \kappa<0.                                   \tag{3.6}
\]

The second sign follows by applying the strict supporting inequality
to \((0,0)\). These statements are elementary supporting calculations,
not an entropy Gaussianity theorem.

Combining (3.4) with the stipulated EPnI gives a precise unpenalized
variational reformulation. For independent finite-energy inputs define

\[
 \mathcal D_{a,b}(A,B)
   =S(C)-pS(A)-q_0S(B)-n\kappa.                                  \tag{3.7}
\]

Then \(\mathcal D_{a,b}\ge0\) on the entire independent-input domain.
It vanishes **exactly** at EPnI equality pairs with input entropies
\(ng(a),ng(b)\). To prove this, split it into the nonnegative EPnI
deficit and the supporting-plane slack in (3.4); strictness fixes the
input entropy vector. Thus proving Gaussianity of every minimizer of
(3.7) would pay NG. Merely knowing its minimum value does not do so.

## 4. Complete classification within the Gaussian inputs

**Proposition G (technical, complete at its stated Gaussian scope).**
For every finite \(n\), all finite-energy Gaussian inputs, and
\(0<\eta<1\), the equality class is exactly that in Target T.

**Proof.** Subtract means. Let the increasingly ordered symplectic
eigenvalues of \(V_A,V_B,V_C\) be \(\alpha_i,\beta_i,\gamma_i\), all
at least \(1/2\). Their entropies are sums of
\(g(\alpha_i-1/2)\), etc. Hiroshima's Theorem 1, equation (65), says
that the symplectic eigenvalue vector of a sum weakly supermajorizes
the sum of the increasingly ordered symplectic eigenvalue vectors.
Applied to \(\eta V_A+(1-\eta)V_B\), it gives

\[
 S(C)\ge\sum_{i=1}^n
   g\bigl(\eta(\alpha_i-\tfrac12)+(1-\eta)(\beta_i-\tfrac12)\bigr)
 \ge n f(S(A)/n,S(B)/n).                                         \tag{4.1}
\]

The first step uses that \(g\) is increasing and concave; the second
is Jensen for Section 3. This is precisely the inequality chain in the
older thesis, now keeping its equality obligations.

Suppose \(a\ne b\) and equality holds. Strict Jensen at the
off-diagonal barycenter shows

\[
 \alpha_i=a+1/2,\qquad \beta_i=b+1/2\quad\text{for every }i.         \tag{4.2}
\]

The first partial-sum inequality in Hiroshima's theorem now gives
\(\gamma_1\ge c+1/2\), so all \(\gamma_i\ge c+1/2\). Equality of
the entropy in (4.1), and strict increase of \(g\), force all
\(\gamma_i=c+1/2\).

It follows that

\[
 \det(V_C)^{1/(2n)}=c+1/2
 =\eta\det(V_A)^{1/(2n)}+(1-\eta)\det(V_B)^{1/(2n)}.               \tag{4.3}
\]

The determinant Minkowski inequality is strict for nonproportional
positive definite matrices. For completeness, conjugate by \(V_A^{-1/2}\),
let \(\theta_j>0\) be the eigenvalues of the conjugated \(V_B\), and
apply strict convexity of
\(u\mapsto\log(\eta+(1-\eta)e^u)\) to \(u_j=\log\theta_j\).
This proves the determinant inequality and shows that equality requires
all \(\theta_j\) equal. Hence (4.3) implies

\[
 V_A/(a+1/2)=V_B/(b+1/2)=G.
\]

Williamson's theorem and (4.2) say that every symplectic eigenvalue of
\(G\) equals one; therefore \(G=SS^T\) for a real symplectic \(S\).
This is (G), including the one-pure-input endpoint.

For \(a=b\), assume first that \(V_A\ne V_B\). The mixture of the two
centered Gaussian states with weights \(\eta,1-\eta\) has covariance
\(V_C\). The Gaussian with a given covariance maximizes entropy, while
strict entropy concavity gives entropy strictly larger than
\(\eta S(A)+(1-\eta)S(B)\) for that nontrivial mixture. Thus
\(S(C)>S(A)=ng(a)\), contrary to equality. The maximum-entropy fact also
includes pure Gaussian modes: in Williamson coordinates, a mode with
zero expected number is vacuum and factors from the rest; for the
remaining modes the product thermal Gibbs inequality gives the bound.
Consequently \(V_A=V_B\). The converse in both cases was already
verified in Section 2. This proves Proposition G. \(\square\)

No claim of new substantial contribution is made for Proposition G.
Its operations are Hiroshima's majorization, the thesis's strict
convexity, the classical determinant inequality, and Gaussian entropy
maximization. It does, however, prevent an incorrect extremal target:
equal-entropy multimode Gaussian equality includes anisotropic
symplectic spectra, whereas unequal-entropy equality does not.

## 5. First attempted bridge: doubling and conditional entropy

The linear equality proof uses a doubling identity whose conditional
entropy remainder is nonnegative by conditional linear qEPI. For the
supporting functional (3.7) the same algebraic identity persists, but
the needed nonnegativity fails. The following are analytic
counterexamples to that proof step, not counterexamples to Target T.

### 5.1 Failure even with finite-energy quantum Markov inputs

For a memory \(M\), write

\[
 \mathcal D_{a,b}(A,B\mid M)
   =S(C\mid M)-pS(A\mid M)-q_0S(B\mid M)-n\kappa.                  \tag{5.1}
\]

There is no universal inequality \(\mathcal D_{a,b}(A,B\mid M)\ge0\)
under finite input energy, finite \(S(M)\), and
\(I(A;B\mid M)=0\), for any fixed unequal reference levels \(a,b\).

Indeed, let \(AM_A\) and \(BM_B\) be independent purifications of
\(\tau_R\), and set \(M=M_AM_B\). Every relevant entropy is finite.
The product of the two groups gives \(I(A;B\mid M)=0\) by the entropy
chain rule, and

\[
 S(A\mid M)=S(B\mid M)=-ng(R).
\]

The two marginal inputs are identical thermal states, so both output
marginals are \(\tau_R\). The global \(CEM\) state is pure. Hence

\[
 S(C\mid M)=S(E)-S(M)=-ng(R),\qquad
 \mathcal D_{a,b}(A,B\mid M)=-n d\,g(R)-n\kappa.                   \tag{5.2}
\]

Since \(d>0\), (5.2) is strictly negative for all sufficiently large
finite \(R\). This is a finite-energy Gaussian construction, with
no limiting or infinite-entropy memory needed. One can take any
\(R\) with \(g(R)>-\kappa/d\). The exact interval checker verifies
the explicit instance \(a=1/10,b=1,\eta=1/2,R=100\).

This does not conflict with the primary conditional qEPI theorem, whose
linear coefficients sum to one and whose general affine correction is
the relative-entropy expression in its equation (106). Here
\(p+q_0<1\). In particular, one must not substitute (3.3) for the
two complementary coefficients in that theorem.

### 5.2 A stronger failure on the actual extremizer-plus-thermal circuit

The previous example could be dismissed as a memory class larger than
the intended doubling construction. The following obstruction has
exactly the doubling provenance, and both initial pairs already minimize
the correct supporting functional.

Take one mode, unequal \(a,b>0\), and a common one-mode squeeze with
\(S_s=\operatorname{diag}(s,s^{-1})\), \(s>1\). Let pair 1 be

\[
 (U_s\tau_aU_s^*,\ U_s\tau_bU_s^*),
\]

and pair 2 be \((\tau_a,\tau_b)\). Both have the prescribed entropy
levels and satisfy \(\mathcal D_{a,b}=0\), by the already checked
sufficiency of (G). Mix the two A ports on a balanced beam splitter,
and likewise the two B ports, obtaining plus/minus ports. The A group
and B group are independent, and with \(M=A_+B_+\) one has
\(I(A_-;B_-\mid M)=0\).

Let \(C_+,E_+\) and \(C_-,E_-\) denote the subsequent
\(\eta\)-beam-splitter outputs. Entropy chain rules and the commuting
two circuit orders give, for **any** fixed scalar coefficients
\(p,q_0,\kappa\),

\[
 \begin{split}
 &\mathcal D_{a,b}(A_1,B_1)+\mathcal D_{a,b}(A_2,B_2)\\
 &\quad=\mathcal D_{a,b}(A_+,B_+)
       +\mathcal D_{a,b}(A_-,B_-\mid M)
       +I(C_-;E_+\mid C_+).                                     \tag{5.3}
 \end{split}
\]

This is the algebra in Li's Lemma 3: the A entropies combine to
\(S(A_1)+S(A_2)\), the B entropies likewise, and the C terms combine
after the conditional mutual information is added. The two constants
on each side total \(-2\kappa\). No assumption \(p+q_0=1\) is needed
for this identity; it is needed for the usual sign argument.

The plus input covariances have the common shape

\[
 V_{A_+}=(a+1/2)(S_sS_s^T+I)/2,\qquad
 V_{B_+}=(b+1/2)(S_sS_s^T+I)/2.
\]

Its symplectic scale is \(t=(s+s^{-1})/2>1\). Therefore their photon
entropy parameters and the C-plus parameter are

\[
 a_t=t(a+1/2)-1/2,\quad b_t=t(b+1/2)-1/2,\quad
 c_t=t(c+1/2)-1/2.
\]

This plus pair is Gaussian EPnI equality at **different** input entropy
levels. Strict supporting-plane inequality (3.4) consequently proves

\[
 \mathcal D_{a,b}(A_+,B_+)
   =g(c_t)-p g(a_t)-q_0g(b_t)-\kappa>0.                           \tag{5.4}
\]

The left side of (5.3) is zero, and its conditional mutual information
is nonnegative. Equations (5.3)--(5.4) force

\[
 \mathcal D_{a,b}(A_-,B_-\mid M)<0.                               \tag{5.5}
\]

Thus the sought sum of nonnegative remainders fails **even for known
extremizers paired with the thermal auxiliary at the original entropy
levels**. This is not merely a failure on an unrelated quantum memory.
The exact checker uses \(s=2,a=1/10,b=1,\eta=1/2\), for which
\((a_t,b_t,c_t)=(1/4,11/8,13/16)\), and certifies the strict sign in
(5.4) with rational logarithm intervals.

One could instead try to choose an auxiliary matching an unknown common
symplectic shape. Establishing that such a shape exists is already part
of NG; it is not supplied by the known doubling argument. I found no
valid replacement sign inequality that keeps the full optimizer family.

Also, independence of the **original** two outputs cannot be the missing
criterion. For the plain unequal thermal pair,

\[
 I(C;E)=n\{g(c)+g((1-\eta)a+\eta b)-g(a)-g(b)\}>0,                \tag{5.6}
\]

by strict concavity of \(g\), while the EPnI deficit is zero. This
already excludes an automatic transfer from the exact product-output
Darmois--Skitovich criterion. I117 had explicitly retained this
unequal-temperature correlation issue; (5.6) is not claimed as new.

## 6. Second attempted bridge: variational Gaussianity

The supporting reformulation (3.7) makes the unpenalized minimizers
concrete. I attempted to use the pinned proof's Gibbs, Hessian,
four-weight interpolation and relaxation operations directly at such a
minimizer. There are two precise unpaid passages.

First, the source's component entropy-Hessian estimate is proved at
faithful, coercively regularized Gibbs minimizers of its functional
\(J_\zeta\). It uses an output thermal replacement, a positive
relative-entropy/energy penalty, a fourth-moment penalty, and exact
logarithm identities. An arbitrary equality state for (3.7) has none
of those conclusions by hypothesis. Setting all those parameters to
zero in the equations does not prove their domain hypotheses or preserve
the original minimizer. Common squeezing gives a noncompact family
of actual minimizers with fixed entropy and unbounded energy, so
coercivity cannot simply be inferred from a sublevel of (3.7).

Even after the needed regularity were established, the zero-penalty
stationarity calculation would give equality of the output and weighted
input defect norms, not vanishing of both input defects. Nontrivially
squeezed thermal pairs are genuine equality states and have nonzero
defects relative to the unsqueezed thermal references. A useful proof
would have to classify saturation of the interpolation and slice
comparisons, allowing a common quadratic Gaussian shape, rather than
reusing the source's positive-penalty coercive vanishing conclusion.

A conceivable approach is to identify a suitably defined output
logarithmic score, show from saturation that its beam-splitter lift
is a sum of one-port observables, and prove that its modular
commutators with all quadratures are linear. Such a conclusion could
force quadratic logarithms and hence Gaussianity. This report supplies
neither the saturation-to-score statement nor its unbounded-domain
justification. They are explicit remaining obligations, not lemmas
silently assumed in a complete proof.

### 6.1 All number moments do not repair the score-domain passage

Here is a concrete faithful, centered, one-mode state of finite energy
and **every** finite number moment for which the thermal-metric score
dual norm at reference \(r=1\) is infinite. This is an obstruction to
deducing source regularity from moment finiteness alone, not an EPnI
equality state or a counterexample to NG.

Let

\[
 x_k=2^{-k-1},\quad y_k=2^{-4^{k+1}},\quad
 Z=\sum_{k\ge0}(x_k+y_k),\quad
 \rho=Z^{-1}\sum_{k\ge0}
       (x_k|2k\rangle\langle2k|+y_k|2k+1\rangle\langle2k+1|).
                                                                    \tag{6.1}
\]

All probabilities are positive and \(1<Z\le16/15\). Geometric decay
of the even weights and faster decay of the odd weights give every
number moment. Entropy is finite by the finite-energy Gibbs bound.

For the annihilation matrix entry \((l,m)=(2k,2k+1)\), the source's
modular frequency, at \(h(1)=\log2\), is

\[
 v_k=4^{k+1}-k-1,
 \qquad K_k=(2y_k-x_k)/Z\le-x_k/(2Z).
\]

On this finite matrix coordinate the squared dual contribution is
exactly

\[
 (1-v_k)K_k(2k+1)
 \ge Z^{-1}(2k+1)2^{k-1}.                                       \tag{6.2}
\]

To verify (6.2), use
\(v_k-1=4^{k+1}-k-2\ge2\,4^k\) and \(x_k/2=2^{-k-2}\).
Equivalently, the coordinate dual calculation is
\(K_k^2/[h(1)\ell(p_{2k},2p_{2k+1})]=(1-v_k)K_k\), using the
logarithmic mean. Finite collections of these off-diagonal coordinates
are admitted centered finite-block tests. Their squared dual norms
already dominate arbitrarily large partial sums of (6.2). The full
dual norm is therefore infinite. No formal cyclic trace of an
undefined unbounded product is used.

### 6.2 No finite mutual-information penalty removes independence

Another attempted transfer was to a joint-state Gaussian
Brascamp--Lieb/entropy extremality statement by penalizing violations
of input independence. There is no finite constant \(L\ge0\) for
which the following bound holds for all finite-energy **joint** inputs:

\[
 S(C)-pS(A)-q_0S(B)+L I(A;B)\ge n\kappa.                         \tag{6.3}
\]

Here it suffices to take one mode and any unequal \(a,b>0\). Consider
the centered gauge-invariant two-port Gaussian state with covariance

\[
 V(t)=\begin{pmatrix}(a+1/2)I_2&t I_2\\t I_2&(b+1/2)I_2\end{pmatrix},
 \qquad |t|<\sqrt{ab}.
\]

Its marginals remain \(\tau_a,\tau_b\). A passive rotation
diagonalizes its port matrix, with photon numbers

\[
 m_\pm(t)=\frac{a+b\pm\sqrt{(a-b)^2+4t^2}}2>0.
\]

Thus
\(I_t=g(a)+g(b)-g(m_+(t))-g(m_-(t))=O(t^2)\), whereas the retained
output is thermal with photon number
\(c+2\sqrt{\eta(1-\eta)}t\). Relative to equality at \(t=0\), the
left side of (6.3) minus its right side is

\[
 2\sqrt{\eta(1-\eta)}h(c)t+O(t^2)+L O(t^2),
\]

which is negative for sufficiently small negative \(t\), for every
fixed finite \(L\). The covariance remains strictly physical.
This proves the failure of (6.3) at its stated general scope. The
checker gives exact rational-eigenvalue witnesses for
\(L=0,1,10,100,1000\). The analytic first-order argument proves the
all-finite-\(L\) statement; a finite list of witnesses alone would not.

This does not refute (3.7), whose inputs must be independent. It blocks
this particular route to importing an unconstrained joint-state
Gaussian-optimizer theorem. No conclusion about every possible
Brascamp--Lieb method is drawn.

## 7. Source contracts and actual reading

All upstream mathematics is accepted as true at
`openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.
Fresh upstream requests used only raw URLs at that commit. Every
retrieved text file was checked against its Git blob in the complete
`preprints-tree.json`; catalogue prose was used only for selection.
All copies are beneath this directory. `receipts/upstream-fetch.json`
records paths, exact URLs, bytes, Git SHA-1 and SHA-256. The complete
tree was parsed to identify the manuscript family and companions;
it was not treated as a claim to have read all manuscripts.

The operative pinned paper is
`preprints/The-entropy-photon-number-inequality-September-24-2026/`:

* `build/sections/00-introduction.tex`: `thm:epni`,
  `cor:thermal-attenuator`, exact scope and the explicit uniqueness
  limitation; entire file read.
* `01-preliminaries.tex`: `lem:energy-compactness`,
  `lem:gibbs-variational`, `prop:thermal-mixing`; entire file read.
* `02-interpolation.tex`: `thm:interpolation`, the parallel-sum proof,
  `int:stieltjes`, and final scalar minimization; entire file read.
* `03-minimization.tex`: `prop:regularized-minimum`,
  `eq:log-identity`, `prop:hessian`,
  `eq:relative-entropy-difference`; entire file read.
* `04-metric.tex`: `prop:metric`, `lem:dual-finiteness`,
  `lem:weak-traces`, `prop:defect-estimate`; entire file read.
* `05-stationarity.tex`: `eq:exact-cancellation`,
  `eq:vanishing-defects`, and final thermal-limit argument; entire
  file read.
* `06-broadcast.tex`: lines 1--69 and a full-file equality/uniqueness
  lexical screen. This companion application supplies no equality
  classification used here; the rest was not semantically read.
* `build/references.tex`: entire bibliography read for primary leads.

The bounded structural screen used the exact `thm:main` and introduction
of `Universal-strong-Kadison-Kastler-stability-September-23-2026`, plus
its comparison-section search. The other fetched files from that family
were collected for possible use but are **not represented as read** or
as dependencies of the selected result.

Actual primary literature, retained as unmodified HTML plus deterministic
reading views:

* **[De Palma, arXiv:1710.09395v1](https://arxiv.org/html/1710.09395v1)**, Appendix A.8, (A.69)--(A.84):
  symplectic comparison followed by joint strict convexity. This is
  the decisive older proof-operation comparison for Proposition G.
* **[Hiroshima, arXiv:quant-ph/0511006v3](https://arxiv.org/html/quant-ph/0511006v3)**, Section V, Lemma 1 and
  Theorem 1, equations (47)--(66), including their proofs. The theorem
  concerns all real positive definite matrices, so it applies also
  to Gaussian covariances with pure modes. There is no asserted
  equality classification in that theorem that is silently substituted
  for the argument in Section 4.
* **[Li, arXiv:2609.40061v1](https://arxiv.org/html/2609.40061v1)**, Theorems 1--2, Section 1.2, Section 3.1
  and Lemma 3 through its proof, and Appendix B Proposition 14.
  These are linear/exponential equality and conditional doubling/
  product-output interfaces. Its exact finite-energy equal-entropy
  theorem is credited, not counted as a new proof here.
* **[Cuesta, arXiv:1902.05298v1](https://arxiv.org/html/1902.05298v1)**, Theorem 7/Corollary 8 and their
  finite-second-moment characterization proof; Theorem 9 and its
  assumptions. Product outputs are the hypothesis. The approximate
  theorem requires all moments and has second/fourth-moment-dependent
  constants. It supplies no NG implication from EPnI equality.
* **[De Palma--Trevisan, arXiv:1706.00440v2](https://arxiv.org/html/1706.00440v2)**, Theorem 6.1, (104)--(110)
  and start of its proof: finite energy, finite memory entropy,
  conditional independence, complementary affine coefficients and
  their correction term. No conditional EPnI is imported.
* **De Palma--Trevisan--Giovannetti--Ambrosio,
  [arXiv:1803.02360v1](https://arxiv.org/html/1803.02360v1)**, Sections 5.2--5.3 and the start of 7.1.
  The EPnI and sharp quantum Young inequalities are formulated
  separately there; the review's conjectural Young inequality is
  not treated as a proved equality theorem.

This report's primary comparisons concern these explicit versions.
The failed direct requests to two institutional PDF URLs (HTTP 403)
are recorded; neither PDF is claimed read. The successful arXiv HTML
requests supplied the actual primary text. `receipts/read-extents.json`
binds the reading-view line ranges and operative labels. No PDF
extraction, hypothetical current-version upgrade, or exhaustive
worldwide search is claimed.

I read the campaign's 4/10 ledger, the accepted-results/rejection ledger,
and the relevant I82, I114 and I117 reports at the scopes recorded in
the read receipt. Frozen context copies preserve their dates/counts;
historical counts in those older reports are not today's campaign count.

## 8. Executable support, integrity, and final handoff

Run from this directory:

```bash
python -B checks/check.py
python -B checks/verify_manifest.py
```

The first command is read-only by default. It recomputes and compares
`receipts/checks.json`. Decisions use exact fractions and certified
logarithm intervals, not binary floating-point signs. Logarithms are
range-reduced to \([1,2]\) and bounded by 100 terms of the atanh series
with its geometric remainder. Decimal values in the receipt are for
orientation only; certified dyadic endpoints are also recorded.

The controls cover the explicit conditional-memory sign, strict plus
deficit for the actual extremal doubling circuit, thermal output
correlations, five finite mutual-information-penalty counterexamples,
a rational internally correlated two-mode common symplectic covariance,
a deliberately different-shape determinant control, 25 exact balanced
beam-splitter Fock output laws with energy/normalization/entropy signs,
and six finite lower bounds from the divergent-score construction.
The general analytic arguments, not these finite controls, justify
the quantified supporting claims.

`inputs-manifest.json` binds every frozen input byte string. The
`outputs-manifest.json` binds the original report, scripts, reading
views/receipts and original rights notice, with explicit exclusions
for the output manifest itself and the final seal. `seal.json` binds
both manifests and the resulting full owned inventory without a
self-hash. The verifier checks the inventory, hashes, upstream Git
blobs, and deterministic HTML reading-view conversions. It does not
repair, fetch, reseal, or modify a shared index.

No formalization is represented as a certificate. Meaningful future
Lean support could cover the finite covariance algebra and scalar
supporting identities, but the unpaid step is the infinite-dimensional
NG implication, not those finite calculations. There is no proposed
Lean axiom pretending to pay it.

**Handoff:** Target T remains open in this investigation. The exact
remaining task is NG, with Gaussian equality and the equal-entropy
primary theorem already separated. A proof must preserve the common
symplectic optimizer family, handle arbitrary finite-energy states,
and supply an equality mechanism beyond the failed conditional-sign
and finite-information-penalty shortcuts. Proposition G and the
obstruction proofs are retained as technical research only. No
independent proof/contribution/manuscript gate or acceptance is claimed.
