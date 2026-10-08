# H003 raw Grok section review

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h003-lift-section-review-grok-20261008-r1`
Read-only/no-experiment brief. Report nevertheless includes an unrequested tiny
formula witness without commands, source, counts or retained output; not adopted
as experiment evidence. Recurrence/derivative assertions need correction below.

The corrected \(D/J\) formulas are right, and this family still has no concentration mechanism. A conditional \(O(q^{1/3}\mathrm{polylog})\) solver is valid arithmetic under an unsupported interval hypothesis. It does not change the full-size assessment: verified gain remains none. The proposed sweep of all 252 sections at \(q\le 61\) would not change it either.

Checked on one ordinary curve only as a formula witness, not as the concentration pilot: \(p=5\), \(y^2=x^3+2x+1\), \(\#E=7=q\neq p\). No histograms were run.

## What holds

The \(y\)-lift is the first-order curve equation. With canonical representatives and \(e=(r^3+A_0 r+B_0-v^2)/p\),

\[
\hat y=v+p\frac{e+ax+b+(3x^2+A)\varphi}{2y}.
\]

For odd \(q\neq p\), \(\psi_q\in\mathbb{Z}[A,B,x]\) is separable of degree \((q^2-1)/2\) on \(E[q]\): every nonzero \(q\)-torsion \(x\)-coordinate is a simple root, so \(J=\partial\psi_q/\partial x\neq 0\) at every \(R\in G\setminus\{O\}\). “Simple roots” is automatic. Multivariable Hensel gives

\[
x_\tau=r-p\frac{D+aU+bV}{J},\qquad D=\psi_q(r;A_0,B_0)/p.
\]

Omitting \(J\) is wrong. At \(R=(1,3)\), \(D\equiv 3\), \(J\equiv 4\), \(D/J\equiv 2\), and \(x_\tau\equiv 16\pmod{25}\) is a root of \(\psi_7\). The omitted-\(J\) value \(x\equiv 11\) has \(\psi_7\equiv 5\neq 0\).

The fiber coordinate of \(s-\tau\) for \(\omega=dx/(2y)\), equivalently \(z=-x/y\), is exactly

\[
g=\frac{(D+aU+bV)/J+\varphi}{2y}.
\]

The sign is the positive one: \((x_s-x_\tau)/(2y)\equiv p\,g\pmod{p^2}\). At this \(R\), both sides are \(10\pmod{25}\). A global sign flip would only send \((C_k,\lambda)\mapsto(-C_k,-\lambda)\). Pointwise, the displayed sign is the one that matches \(z(s-\tau)/p\).

Weighted homogeneity \(\psi(\lambda^4 A,\lambda^6 B,\lambda^2 x)=\lambda^{q^2-1}\psi\) gives \(2xJ+4AU+6BV=0\) on roots, hence \(4A\,h_A+6B\,h_B=-2F_1\). The grid direction \((a,b,\varphi)=(4Aw,6Bw,2wx)\) changes no \(g\). It is one linear dependence among the five features. At \(j=0\) it moves the \(b\)-line only, so the \(a\)-line still changes \(g\). At \(j=1728\) the surviving modulus is \(b\). Those are real deformations of the lifted curve. Counting them as extra signals would be double-counting; deleting the whole \((a,b)\) family at \(j\in\{0,1728\}\) would be wrong.

\(\varphi=-(D+aU+bV)/J+2yf\) gives \(g=f\) for every \(f\). An unrestricted section is just a predictor written in fiber coordinates. That is not a hardness proof against a named \(f\).

Negation equivariance for families 1 and 2 is real: \(D,J,U,V,\varphi\) depend on \(x\) only, so \(g(-R)=-g(R)\). For integer representatives, \(C_{q-k}=q\,g(P)-C_k\). In \(\mathbb{F}_p\), the pairing used by a cyclic dictionary is \(C_{q-k}\equiv (q\bmod p)\lambda-C_k\). Family 3 is not odd.

The small-image bound is right and sharp in exponent. For \(g=1+(x\bmod B)\), each fixed correction admits at most \(B\) residue classes of \(k\bmod p\), and each class meets \(\{1,\ldots,q-1\}\) in at most \(L=\lceil q/p\rceil\) canonical lifts. Thus \(|C|\ge\beta(q-1)/(BL)\). In the target regime \(q\approx p\) one has \(L\in\{1,2\}\) and, for \(B=q^\gamma\),

\[
\alpha\ge 1-\gamma
\]

up to the constant factor \(\beta/L\). For \(\gamma<1/2\) this forbids every dictionary with \(\alpha<1/2\), and also every exponent between \(1/2\) and \(1-\gamma\). The writeup’s “excludes \(\alpha<1/2\)” is the weak form. Family 3 cannot feed the solver’s \(M=q^{1/3}\) hypothesis. The only group homomorphism \(G\to\mathbb{F}_p\) is \(0\) because \(q\neq p\), and \(g=0\) has \(\lambda=0\), so eligibility rejects the one perfectly concentrated case. None of this touches the 243 degree-\(\le 2\) sections or the 9 Teichmüller sections, whose images are not small by this counting.

## Recurrence repair

\(O(\log q)\) arithmetic in \(\mathbb{Z}/p^2\) is the right cost for a constant-size window on the binary expansion of \(q\). Two corrections:

The window has to be evaluated at a point of a lifted curve over \(\mathbb{Z}/p^2\), for example \(x=r\) and \(y\) corrected by \(e,a,b,\varphi\). The identities are curve identities. The raw representative \((r,v)\) lies on the curve only modulo \(p\). At \((1,3)\), which is canonical and not integral on the curve, the same recurrence returns \(\psi_7\equiv 0\pmod{25}\). The on-curve value is \(15\), so the carry read off the raw point is \(D\equiv 0\) instead of \(D\equiv 3\).

Closing a doubling window uses

\[
\psi_{n+3}=\bigl((2y)^2\psi_{n+2}\psi_n-\psi_3\psi_{n+1}^2\bigr)/\psi_{n-1}
\]

as well as the even step’s division by \(2y\). So the recurrence divides by more than \(2y\). For \(0<i<q\) and \(R\neq O\), \(\psi_i(\hat R)\) is a unit in \(\mathbb{Z}/p^2\), because every non-identity point has order \(q\). The final \(\psi_q\) is divisible by \(p\) and must stay in the numerator. Point-difference denominators \(x_1-x_2\) are a different hazard and do not appear. Derivatives modulo \(p\) are difference quotients under \(x\mapsto x+p\), \(A\mapsto A+p\), \(B\mapsto B+p\), or the termwise derivative of that same unit-divided recurrence, holding \(y\) independent of \(x\). Reducing \(y^2\) to the cubic before differentiating changes \(\partial\psi_q/\partial x\).

On the formula witness, \(\psi_1,\ldots,\psi_6\) at the lift of a generator are units and \(\psi_7\) is not. The Euler check \(2xJ+4AU+6BV\equiv 0\) and the \(a=1\) Hensel root both match the repaired derivative.

## Conditional solver

The probability lower bound is right: one hidden cyclic interval of \(M\) values, eight uniform training scalars, \(\eta=1-(1-\beta)^8\), an independent uniform target, and one section drawn from \(T\), gives success probability at least \(\eta\beta/T\) on a hypothesis-true instance. Containment needs cyclic arithmetic. A training hit at an endpoint covers an interval of length \(M\) by a window of radius \(M\), so the searched set has size \(\Theta(M)\) per training hit, not \(M\). With eight hits the width factor is about \(16\). Verification \(k'P=Q'\) is required, because that window properly contains the hidden interval.

Naive work \(O\bigl(T(\eta\beta)^{-1}(\log q+\log p+ML\log q)\bigr)\) counts a scalar multiplication per candidate. Streaming is also \(O(ML+\log q)\) group additions per trial once wraps are explicit. Let \(\delta=\lambda^{-1}\bmod p\) and let \(r\in\{0,\ldots,p-1\}\) be the running residue. The precomputed points \(\delta P\) and \(pP\) update one lift by

\[
r\leftarrow r+\delta,\qquad P\leftarrow P+\delta P,
\]
and if \(r\ge p\) then \(r\leftarrow r-p\) and \(P\leftarrow P-pP\). The second canonical lift \(P+pP\) is legal only while \(r+p<q\). For \(p<q<2p\) that predicate toggles as \(r\) crosses \(q-p\). Adding \(\delta P\) with no correction mixes lift classes: on this same \((p,q)=(5,7)\), the step \(4P\mapsto 5P\) has left residue \(4\) and entered the second lift of residue \(0\).

\(L=\lceil q/p\rceil\in\{1,2\}\) whenever \(q\approx p\). Keep it. The \(q=p\) anomalous regime is outside this formula and does not support it.

Under the hypothesis, cap trials at \(\Theta(T/(\eta\beta))\) and the expected cost is \(O(Tq^{1/3})\) group additions after streaming, times a small polylog from section evaluation. \(T=252\), \(\beta=1/4\) and eight samples make the leading constant a few thousand once the width-\(2M\) windows are counted; one training sample is a cheaper constant than eight. Fallback to negation rho keeps a hypothesis-false instance inside \(O(q^{1/2})\) group operations. The conditional exponent is real. It is entirely conditional on the interval hypothesis.

## Mechanism

\(C_k\) does not see the division polynomial. If \(g\) is the \(E_1\)-coordinate of \(s-\tau\) and \(\tau\) is the unique \(q\)-torsion section, then

\[
C_k=\text{coordinate of }k\cdot s(P)-s(kP).
\]

\(D,J,U,V\) cancel. They are an evaluation method for \(g\), not a source of bias. Concentration says that one of these 252 explicit sections is an approximate homomorphism \(G\to\tilde E(\mathbb{Z}/p^2)\) whose defect lies in one cyclic interval of length \(q^{1/3}\) for at least a quarter of the canonical scalars. Equivalently, that explicit \(g\) approximates \(\lambda\) times the integer discrete log to that accuracy.

Nothing in the ansatz forces that. Degree \(\le 2\) corrections and digits \(\{a,b\}\subset\{-1,0,1\}\) are a bounded neighborhood of the coordinate section. The Teichmüller coordinate \(\omega(x)\equiv r^p\pmod{p^2}\) is multiplicative on \(\mathbb{F}_p\) and does not interact with the chord-and-tangent law; the writeup already says so. Negation gives only the reflection above. The exact section with \(g=0\) is \(\varphi=-(D+aU+bV)/J\), a rational function of degree \(\Theta(q^2)\), outside the finite list, and it has no scalar signal.

On curves with an extra automorphism the equivariant members, including pure Teichmüller \(\varphi\), are a separate scoped case. A determinant \(\det=nq\) does not by itself lower-bound fiber sizes; the shortest vector of that rank-2 lattice does, and then \(\alpha\ge 1/2\) for those equivariant sections when the vector is generic. That obstruction stops at \(\mathrm{Aut}\neq\{\pm 1\}\). It does not transfer to ordinary curves whose only automorphism is negation, and trace-one methods do not transfer across \(q\neq p\).

So there is no exact obstruction covering the whole 252-section list on the curves this project actually targets, and there is also no candidate-specific reason to expect interval concentration. The interval shape is what makes eight samples locate a dictionary. A scattered set of size \(q^{1/3}\) would not be recovered by this argument, and nothing about these carries suggests an interval rather than a scattered set.

## What would change the assessment

The proposed histograms would not. For \(q\le 61\), \(M=\lceil q^{1/3}\rceil\) is \(4\) at \(q=61\), and \(\beta q\approx 15\) against a random interval mean near \(4\). A hit that large would be strange, and a miss is what any unstructured function does. Either outcome is an instance at \(q\le 61\). A miss does not forbid a large-\(q\) bias. A hit does not produce a uniform exponent, and it does not leave the curve it was measured on. Running all 252 sections, two curves, and two generators is a look-elsewhere search over a list that was not singled out by a mechanism. The \(60\)-second cap is not the obstacle; the test does not decide the full-size question. It should not be funded.

A finite check that would matter is a proof, or a disproof, of a stated structural claim: that every \(g\) in this list has image of \(k\mapsto C_k\) larger than \(q^{1/2}\), or that one named section obeys an identity strong enough to force an interval of length \(q^{1/3}\). No such identity is on offer. Killing or sparing one section on one toy curve leaves the other sections and the large-\(q\) problem where they are. No narrow cheap experiment changes the full-size conclusion until that mechanism exists.
