# Author proof: flat prescribed-class nonselection on T4

This is a discovery-stage author-proof nominee for the exact six-part statement in THEOREM.md. It is not an independent correctness verdict, a contribution verdict, an accepted finding, or a manuscript/release. The frozen statement is unchanged. The construction and all quantifiers below are on the fixed oriented flat torus; no moving diffeomorphism gauge is used.

## 1. Pointwise algebra and normalization

Write dV=dx1∧dx2∧dx3∧dx4, of total volume one. With the standard Hodge star, U=e12+e34, V=e13-e24, W=e14+e23 form an orthogonal basis of the constant self-dual forms, each of norm squared two. Their pairwise wedge products vanish and each squares to 2dV. Let I and K be the skew endomorphisms defined by g(Iu,v)=U(u,v) and g(Ku,v)=V(u,v). On the coordinate frame, I sends e1 to e2 and e3 to e4, and K sends e1 to e3 and e2 to -e4, with their squares determining the other images. Direct multiplication gives I²=K²=-Id and IK=-KI. Thus

    J(a)=(I+aK)/sqrt(1+a²)

is orthogonal, squares to -Id, and has fundamental form (U+aV)/sqrt(1+a²). This form squares to 2dV, so its complex orientation is the fixed one. Since IK is skew, g(Iv,Kv)=0, and consequently

    U(v,J(a)v)=|v|²/sqrt(1+a²).                         (1)

For any orthogonal J of this orientation with fundamental form F, a real two-form is J-invariant exactly when its self-dual part is a scalar multiple of F. In a J-unitary basis a J-invariant form has Hermitian eigenvalues λ1,λ2. Its self-dual part is ((λ1+λ2)/2)F, its square is 2λ1λ2dV, and its Euclidean norm squared is λ1²+λ2². These formulas follow by diagonalizing the real Hermitian form α(·,J·), or directly from Λ_J^+=RF⊕Λ_g^-.

It follows that an invariant α is positive if its self-dual coefficient is positive and α²>0. Conversely, for a positive invariant α with α^+=q(U+aV), one has q>0 and

    |α|²=λ1²+λ2² <= (λ1+λ2)²=4q²(1+a²).              (2)

These are the classical four-dimensional pointwise operations also used in Source342 and DLZ; no novelty is assigned to them.

## 2. The fixed smooth input functions exist

For example, choose a nonzero nonnegative smooth bump on the circle supported in a proper arc and normalize its integral to one; call it p. Choose a nonzero smooth function χ with 0<=χ<=1 supported inside an open arc where p=0, and put f(x,z)=χ(x)χ(z). This has all the required properties. The proof below works for every p,f in the frozen statement, not just this example.

Let c=∫f. Since f is continuous, nonnegative and nonzero, 0<c<=1, and {f>0} is nonempty and open. The support condition implies that both p(x1) and p(x3) vanish wherever f is positive. In particular f is not constant: p is positive somewhere because its mean is one, and f vanishes at every pair whose first coordinate is such a point.

For 0<=s<=1/4 define

    A_s(x)=s+(1-s)p(x),
    q_s=(A_s(x1)+A_s(x3))/2,
    a_s=s(f-sc),  r_s=sqrt(1+a_s²).

The elementary identities that drive the construction are

    ∫A_s=1,   ∫q_s=1,   q_s f=s f,   ∫q_s f=sc.       (3)

The third equality is pointwise, by the two support conditions. For s>0, A_s>=s and q_s>=s. Also

    |a_s|<=s(1+s)<=5/16,  hence r_s<2.                (4)

## 3. Smooth and uniformly tamed almost complex structures

Set s(t)=exp(-1/t²)/4 for positive t and s(0)=0. The function extends smoothly through zero by setting it to zero for negative t, and every derivative at zero is zero. Its values on [0,1] lie in [0,1/4]. The coefficients a_t=s(t)f-s(t)²c, and all their positive-order t derivatives at zero, therefore vanish. Smooth composition with J(a) proves joint smoothness of J_t and the asserted flatness to every parameter order, including after any fixed number of spatial derivatives.

Equation (1), together with (4), proves U(v,J_tv)>=|v|²/2. U is closed and U²=2dV, so it is a fixed symplectic tamer. It is the fundamental form of J_0=I. Compactness of [0,1]×X implies bounds on each smooth seminorm of J. The background metric is exactly flat throughout, with fixed volume and injectivity radius.

## 4. The fixed-class representatives and their smooth degenerate limit

For s>0 put

    η_s=A_s(x1)e12+A_s(x3)e34+2s²(f-cq_s)e13.          (5)

Each coefficient depends only on coordinates already appearing in its wedge factor. Thus every summand is closed. The first two terms have harmonic averages e12 and e34. The e13 coefficient has average zero since ∫f=c and ∫q_s=1. Hence [η_s]=[U].

One can verify exactness without invoking any unproved Hodge interface. The diagonal differences have primitives P_s(x1)dx2 and P_s(x3)dx4, where P_s'=A_s-1 and P_s is periodic because A_s-1 has mean zero. For a periodic h(x,z) with total mean zero, set

    m(z)=∫_0^1 h(x,z)dx,
    H(x,z)=∫_0^x (h(u,z)-m(z))du,
    M(z)=∫_0^z m(v)dv.

Both H and M are periodic in their respective coordinates, and

    h(x1,x3)e13=d(H dx3-M dx1).

Apply this to h=2s²(f-cq_s). Thus the full class assertion in (5) is constructive.

The self-dual part of (5) is

    η_s^+=q_s U+s²(f-cq_s)V
          =q_s[U+s(f-sc)V]=q_s r_s F_s,              (6)

using q_s f=s f. This proves J_s-invariance. Moreover all wedges involving e13 in (5) vanish, so

    η_s²=2A_s(x1)A_s(x3)dV>0.                        (7)

Its self-dual coefficient q_s r_s is positive. Section 1 now proves that η_s is J_s-compatible; positivity does not rest on a perturbative error bound. In particular all positive t have a compatible representative of the EXACT class [U]. At t=0 the compatible representative U is available independently.

Formula (5) is polynomial in s with fixed smooth coefficients, so composing with s(t) extends η_t smoothly to

    η_0=p(x1)e12+p(x3)e34.

This is closed, J_0-invariant and nonnegative. It vanishes on {f>0}, so it is degenerate. The fixed-class family on the punctured interval has bounded derivatives of every fixed order even though its limit fails to be symplectic. This distinguishes loss of positivity from a necessary blowup of all coefficients.

## 5. A constraint on EVERY compatible representative

Fix t>0 and let α be ANY smooth J_t-compatible symplectic form in class [U]. The pointwise decomposition in Section 1 gives the UNIQUE expression

    α^+=q(U+a_t V),  q=<α,U>/2>0.                    (8)

The constant forms U,V are closed and self-dual. Since [α]=[U], integration of α∧U and α∧V gives respectively 2 and 0. Orthogonality and |U|²=|V|²=2 turn these equalities into

    ∫q=1,   ∫q a_t=0.

Dividing the second equality by the strictly positive scalar s(t), and using the first, yields

    ∫q f=s(t)c.                                     (9)

There is NO division by s at the endpoint; (9) holds for positive t and is then used in a limit. Equation (2) and r_t<2 give |α|<=4q. For δ>0, nonnegativity and (9) imply

    δ ∫_{f>=δ} q <=∫q f=s(t)c.                       (10)

This proves the entire universal assertion, including the normalization and concentration estimate, independently of the particular forms in (5).

## 6. Compactness and every possible limit

Let t_n>0 tend to zero and choose arbitrary compatible α_n in [U]. Their coefficient measures have uniformly bounded total variation because

    ∫|α_n|<=4∫q_n=4.

The space of continuous functions on the compact metric torus is separable. Weak-* compactness of bounded finite Radon measures, followed by a subsequence for the finitely many coefficients, gives weak-* subsequential convergence α_n -> A. The q_n dV likewise converge to ν=<A,U>/2, a positive measure of mass one.

Closedness passes to the distributional limit. Every constant harmonic coefficient is unchanged: the mean of α_n is U, so the mean of A is U. For completeness, this identifies the distributional cohomology class without a regularization assumption. Let D=A-U. Its zero Fourier coefficient is zero. At a nonzero integer vector k, distributional closedness says k^flat∧D_hat(k)=0. Define a distributional one-form by

    β_hat(k)=(2π i |k|²)^(-1) ι_k D_hat(k),  β_hat(0)=0.

Fourier coefficients of a distribution grow at most polynomially, so this defines a distribution; in this case the coefficients of A are even bounded measures. The identity k^flat∧ι_k+ι_k(k^flat∧·)=|k|² Id gives dβ=D. Thus A represents [U] as asserted.

Let R_t be the anti-invariant projection. Its coefficients converge uniformly to those of R_0. Because R_t α_n=0,

    ||R_0 α_n||_measure <= ||R_0-R_{t_n}||_infinity ∫|α_n| ->0.

Hence A is J_0-invariant. To prove nonnegativity, let v be a smooth vector field and φ a nonnegative smooth function supported in a coordinate chart. Then

    ∫φ α_n(v,J_0v)=∫φ α_n(v,J_{t_n}v)+o(1)>=o(1),

where the error tends to zero by uniform convergence of J and the mass bound. Passing to the limit proves that A(v,J_0v) is a nonnegative measure. This is precisely the claimed semipositivity of the measure-valued invariant form.

Finally ∫f dν=lim ∫q_n f=0. Since f>=0, ν is supported on {f=0}. The form A has the same support restriction. Indeed if a smooth test two-form β is supported in a compact subset of {f>0}, then f>=δ>0 there and (10) implies

    |∫<α_n,β>dV| <= 4||β||_infinity s(t_n)c/δ ->0.

A therefore vanishes on {f>0}.

These arguments apply to EVERY subsequential limit, not merely to the explicit family (5). Such a limit cannot be a smooth J_0-compatible form: a positive Hermitian form cannot vanish on a nonempty open set. Equivalently, were α_n to converge distributionally to a smooth J_0-compatible α_0, the functions q_n would converge distributionally to q_0=<α_0,U>/2>0; (9) would give ∫q_0 f=0, contrary to f>=0 and f nonzero. This second argument also excludes distributional convergence without first extracting a subsequence.

A distributionally continuous selection on any [0,epsilon] would provide exactly this forbidden convergence along t_n ->0. Therefore none exists. C0 continuity of coefficients implies distributional continuity, and smooth dependence implies C0 continuity. All the nonselection conclusions follow.

## 7. The changing cohomological kernel

For the fixed flat metric, every closed J_t-anti-invariant two-form is self-dual. A closed self-dual form is also coclosed, hence harmonic. Flat-torus Fourier analysis shows that harmonic forms are constant, so such a form is uU+vV+wW for constants u,v,w. It is anti-invariant precisely when it is orthogonal to F_t, namely

    u+v a_t(x)=0 for every x.                         (11)

At t=0 this says u=0, giving span(V,W). For positive t the function a_t=s(t)f-s(t)²c is nonconstant, so (11) forces v=u=0, leaving span(W). These constant forms have linearly independent nonzero de Rham classes. Thus the spaces and dimensions in part 5 are exactly as frozen. The positive index is b+=3, given by the basis U,V,W. A constant-kernel-dimension argument cannot be applied across zero.

## 8. The stronger compatible alternative when periods may move

Define, on the ENTIRE parameter interval,

    ζ_t=U+2a_t e13.                                  (12)

It is closed because a_t depends only on x1,x3. Its self-dual part is U+a_t V=r_t F_t, and ζ_t²=2dV. Its self-dual coefficient is positive, so Section 1 proves compatibility. It is smooth and ζ_0=U. Its mean e13 coefficient is

    2∫a_t=2s(t)c(1-s(t)),

giving the stated class formula. For t>0 this coefficient is nonzero. Thus the strongest local construction allowing class changes actually succeeds, explicitly, while the fixed-class alternative is impossible by (9). Averaging within a fixed J, convexity of its compatible fibre, or an individual cohomological cone criterion cannot remove the universal moment constraint across the changing J_t.

## 9. Scope and logical dependency limits

All six assertions in the frozen statement have now been addressed. The only external operations needed to understand the proof are standard exterior algebra, integration on a torus, elementary Fourier de Rham calculus and weak-* compactness of finite measures. Each operative algebraic/cohomological construction is supplied above. The Source342 theorem is accepted as stipulated but is not needed to establish the explicit compatible forms: this is a negative extension test for a parameter-dependent prescribed-class strengthening of its pointwise conclusion.

There is no prescribed-volume claim; the compatible volume (7) degenerates. There is no uniform positive lower bound for compatible forms, although the common tamer, background metric and J have uniform bounds. There is no claim for a constant-rank cohomology stratum, for integrable deformations, or for other dimensions. No conclusion about arbitrary gauges, all cone boundaries or effective rates beyond (9)-(10) is made. The proof supplies an author nominee; independent correctness and separate substantial-contribution assessment remain the parent's work.
