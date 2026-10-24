# Compatible reduction of the unchanged Structural218 submission

This is the contribution review's calculation, conditional on correctness of the entire unchanged THEOREM.md and AUTHOR-PROOF.md. It is not a new nominee, a second research family, a repair, or a correctness verdict. The source truth stipulation is maintained.

## Paid starting operations actually read

Source342 October §2 gives the closed lift B=dd*G+H and §8 proves that (1-BR) preserves exactness for exact input. The full §8 arbitrary-class separation/current pairing/cone proof is paid. Its last example uses the flat basis U,V,W, the normalized self-dual direction, the null-wedge closed correction 2f e13+2k e23, zero means for exact periods, and constant harmonic anti-invariant forms. DLZ 0812.3680v2 §2.2, Lemmas2.4 and2.6, supplies self-dual Hodge reconstruction and the anti-invariant harmonic identification. DLZ1104.2511v1 §§3.3,3.4.3 supplies the metric-related rank computation; §5 and Donaldson math/0607083v1 §2 permit local solutions with positive-plane period freedom. These are actual proof operations, not titles used as substitutes for reading.

## The complete simultaneous construction for every admitted p,f

Write x=x1, z=x3. Let q0=(p(x)+p(z))/2 and D0=p(x)e12+p(z)e34. The hypotheses, with no separability or special-bump assumption on f, give q0>=0, mean(q0)=1, and q0 f=0. The form D0 is closed, has class [U], and is J0-semipositive. The product-coordinate exact primitives follow by integrating p-1 on each circle.

The ordinary convex interpolation D_s=s U+(1-s)D0, 0<s<=1/4, has positive diagonal entries A_s(x),A_s(z), mean one each, class [U], and self-dual trace q_s=s+(1-s)q0. Consequently q_s f=s f and mean(q_s f)=s c.

Apply the source example's e13 correction operation to D_s. For a coefficient h(x,z), D_s+2h e13 is closed. Its self-dual part is q_s U+h V; its square is exactly 2 A_s(x)A_s(z)dV, independently of h, because e13 squares to zero and wedges to zero with both diagonal summands. Its class remains [U] exactly when mean(h)=0. The mean criterion is exact here because h depends only on x,z: h e13 is a two-form pulled back from T2, and its only period is its T2 integral. Equivalently use the explicit periodic primitive in AUTHOR-PROOF §4.

For the frozen desired direction a_s=s(f-s c), the required h is forced to be q_s a_s. Period cancellation is the scalar weighted-mean subtraction

    lambda_s=mean(q_s f)/mean(q_s)=s c,
    h=q_s s(f-lambda_s)=s^2(f-c q_s).

Thus the strongest construction gives exactly the submitted eta_s, not a surrogate or an approximation. For all allowed p,f it simultaneously gives the fixed support relation, concentration of trace away from f>0, zero e13 period, and positive square. There is no elliptic estimate to repair positivity near a degenerate endpoint: square preservation is exact. Normalizing its self-dual direction gives precisely F_s=(U+a_s V)/sqrt(1+a_s^2). DLZ's pointwise decomposition makes it J_s-invariant; positive trace and positive determinant give positivity of both Hermitian eigenvalues.

This is a compatible composition of the source's explicit torus operation with ordinary diagonal convex interpolation, mean subtraction, and four-dimensional algebra. It is more than identifying the proof as elementary: it specifies the complete recipe and reproduces the exact frozen formula uniformly in its stated quantifiers. The source's sine example alone does not assert this target, but there is no residual PDE, nonlocal positivity problem, or additional construction left after this recombination.

## Strongest Hodge alternative actually carried out

For any self-dual sigma with harmonic mean U, DLZ Lemma2.4 constructs the closed representative of [U]

    U+2dd*G_Delta(sigma-U).

If two closed representatives of [U] have the same self-dual part, their difference is closed, exact and anti-self-dual. It is harmonic and hence zero. Take sigma=q_s(U+a_s V). Its harmonic mean is U by the two scalar means above, with no W component. The explicit eta_s is closed, has class [U], and has this self-dual part; hence it is exactly this Hodge reconstruction. In particular, the successful Hodge route and the null-wedge route are compatible, rather than one being dismissed because an unrelated projection loses positivity.

For free periods the submitted zeta_s=U+2a_s e13 is already the source's one-direction correction with no zero-mean requirement: it is closed, has square2dV, self-dual part U+a_s V, and class [U]+2m_s[e13], m_s=s c(1-s). It is smooth through U. If one asks specifically for Donaldson's positive-harmonic-plane freedom instead, the DLZ reconstruction of the same self-dual part is

    U+(2a_s-m_s)e13-m_s e24,

with class [U]+m_s[V]. This is only an evaluation of the classical comparison operator for the submitted J_s, not another nominee. Its square is 2(1+2m_s a_s-m_s^2)dV. Since |a_s|<=5/16 and 0<=m_s<=1/4, its determinant factor is >=1-5/32-1/16=25/32>0. Its trace is positive and it tends to U. The fixed-class obstruction therefore survives a successfully executed, stronger local solvability comparison, while that comparison is allowed to change periods.

## Every remaining frozen conclusion

1. Quaternionic algebra gives J(a)=(I+aK)/r and U(v,Jv)=|v|^2/r. Here c<=1, |a_s|<=s(1+s)<=5/16, so r<2 and the frozen lower bound1/2 follows. Composition with s(t)=exp(-1/t^2)/4 makes every positive-order t derivative zero at0. Smoothness is joint in t and x. The norm bounds are for each fixed pair p,f, not uniform over all such pairs.

2. The construction above gives exact [U] at every positive parameter. Polynomial dependence in s gives the stated eta0=D0, which vanishes on the fixed nonempty open set {f>0}. U separately belongs to the endpoint compatible fibre. The endpoint of the displayed eta family is not required to be symplectic.

3. For any compatible alpha in [U], classical decomposition gives unique alpha^+=q(U+a_sV), q=<alpha,U>/2>0. Pairing with closed constant U,V yields mean(q)=1 and mean(q a_s)=0. At s>0 the second is exactly mean(qf)=s c. Hermitian eigenvalues give |alpha|<=2q r<4q. Markov's elementary inequality gives integral_{f>=delta}q<=s c/delta for every delta>0. No moment equation is imposed by dividing at s=0.

4. The mass bound integral|alpha|<=4 gives sequential weak-* compactness for finitely many coefficient measures on the compact metric torus. Closedness passes to distributions. All constant coefficient means equal U. For D=A-U the zero Fourier mode vanishes and, at nonzero k, beta_hat(k)=(2 pi i |k|^2)^(-1) i_k D_hat(k) gives d beta=D; hence every limit has the stated distributional class. Uniform J_s->J0 and the mass bound pass invariance and nonnegativity to every subsequential limit. The trace measures have integral f tending to0. More explicitly, every smooth test supported compactly in {f>0}, with f>=delta there, pairs with alpha by at most4||test||_infinity s c/delta. Thus every limit is supported in {f=0}. A smooth J0-compatible form has strictly positive trace, so integral q0 f>0. The universal moment identity excludes distributional convergence to every such endpoint, not only U or the chosen eta0. Choosing any positive sequence in any [0,epsilon] proves the exact nonselection assertion; C0 and smooth continuity imply distributional continuity. Limits need not be singular measures: the displayed eta0 is a smooth degenerate example.

5. The DLZ/source harmonic method is exact here. A closed anti-invariant form is flat self-dual harmonic, hence uU+vV+wW with constants. Orthogonality to F_s means u+v a_s=0 everywhere. For s=0 this gives span(V,W); for s>0 nonconstancy of f forces u=v=0, giving span(W). The fixed positive index is3. The kernel jumps from2 to1, so a smooth generalized inverse justified by constant kernel rank does not apply across0.

6. The successful zeta family, its exact period drift2s c(1-s)[e13], its constant positive square and its endpoint U were executed above. Its period drift is positive for every t>0. The obstruction concerns the stipulated class on the stipulated fixed manifold, without a diffeomorphism gauge. No prescribed volume, integrability, arbitrary path, uniform-in-input estimate or non-flat background claim has been inserted.

## Local sections and convexity

For fixed J, positive closed invariant forms are convex, as is their intersection with a fixed de Rham class. This alone produces no varying-J local section. The full source closed lift at J0 does produce a free-class section locally: identify E_J with E_0 using U_J=R_J|E_0, set A_J=U_J^{-1}R_J B_0, and solve with B_0 A_J^{-1}U_J^{-1}R_J. A_0=Id; its operator-norm inverse for sufficiently close smooth J on a fixed Sobolev scale is the usual small-perturbation inverse. Subtracting this closed lift from a compatible base form restores invariance and preserves positivity locally. Its harmonic part is free to move. Parameter-only partitions of unity then preserve the same J at each parameter. The actual companion lemma executes a smoothly varying generalized inverse with a rank-two kernel; both companion versions have equal05-families bytes. Neither that rank hypothesis nor exact-class local solvability holds across the submitted endpoint. The successful explicit reconstructions above show concretely what survives when periods may move.

## Conditional contribution assessment recorded while work continues

The complete compatible reduction supports TECHNICAL, conditional on full correctness of the entire unchanged statement AND submitted proof. This is not a correctness determination. The geometric nonselection conclusion is sharper than the source's stated torus example; that fact does not leave an indispensable nonroutine operation after the explicit recombination. No project-wide novelty or worldwide priority conclusion follows. The final review must also retain actual primary/history access limits and all accidental exposures.
