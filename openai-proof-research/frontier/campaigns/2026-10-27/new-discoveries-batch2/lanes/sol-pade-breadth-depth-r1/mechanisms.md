# Sustained Padé mechanisms (auxiliary, uncredited)

1. **Reverse-Bessel recurrence.** With q0=1 and q1=1-z/2,
q_m=q_(m-1)+z² q_(m-2)/[4(2m-1)(2m-3)], m≥2.
This follows coefficientwise from factorials (the script checks m2..41 exactly; the factorial substitution gives the general identity). Put a_m=1/[4(2m-1)(2m-3)]. Then
q_(m+2)= (1+a_(m+2)z²)q_m+a_(m+1)z²q_(m-1).
The positive signs in the denominator do not become positive signs on inversion. Indeed c_(m,2)=m/[4(2m-1)] and
c_(m+2,2)-c_(m,2)=-1/[2(2m-1)(2m+3)]<0.
So both coefficientwise increasing reciprocal induction and a coefficientwise nonnegative ratio q_m/q_(m+2) fail already at degree2. This is an obstruction to those induction invariants, not to more elaborate paired induction. Direct renewal 1/q_m=1/(1-K) also has [z²]K=-(m-1)/[4(2m-1)]<0.

2. **Logarithmic/exponential positivity.** The factorial coefficients give
z q_m''+(z-2m)q_m'-m q_m=0.
For h=-q_m'/q_m=Σh_nz^n, h0=1/2, h1=1/[4(2m-1)], h2=0, and
(n-2m)h_n=Σ_(i=1)^(n-2)h_i h_(n-1-i), n≥2.
In particular [z4]log(1/q_m)=-1/[64(2m-1)²(2m-3)]<0 for m≥3. Thus exp of a nonnegative coefficient series cannot directly supply the result. The singular equation at n=2m leaves a compatibility/free coefficient issue; it is not a universal positive induction.

3. **Positive Laplace integral cannot work literally.** Already q3=1-z/2+z²/10-z³/120. Its derivative is -((z-4)²+4)/40 on the real line, so it has a unique real root R∈(4,5). The other roots are α±iβ with α=(12-R)/2<R, β≠0, and are simple. A positive measure μ on [0,∞) with 1/q3(-s)=∫e^(-st)dμ(t), s≥0, would have finite moments from derivatives at zero. For 0<x<R, monotone convergence would give ∫e^(xt)dμ=Σc_n x^n=1/q3(x), hence holomorphy for Re z<R of the moment-generating transform. But 1/q3(z) has nonreal poles α±iβ inside that half-plane. Analytic continuation from zero contradicts holomorphy. Therefore a literal positive Laplace representation is impossible, even if the target coefficients are all positive. The argument is an auxiliary classical obstruction, not a new source result. More general positive combinatorial representations are not excluded.

4. **Even-product route, exact failure beyond low orders.** Set D_m(w)=q_m(z)q_m(-z), w=z². Odd terms cancel and the coefficient formula is
d_j=(-1)^j binom(m,j) (2m-j)! m! (2m-2j)! / [(2m)!² (m-j)!].
It follows by expanding the two factorial sums; product_route.py independently checks the formula against convolution for odd m≤19. Since q_m(-z) has strictly positive coefficients, coefficientwise nonnegativity of 1/D_m would suffice for the endpoint. That stronger assertion is FALSE:
[w10]1/D_11(w)=-21866269/9888422815022969014815189447475200.
The original c_(11,20) remains positive: multiplication by q11(-z) compensates this negative term. Similar isolated negative entries occur at w^(m-1) for tested m13,15,17,19. This is a useful exact obstruction, not a source counterexample and not a count.

**Next mechanism after these failures.** Retain the even and odd numerator polynomials E_m(w)=Σω_(2j)w^j and O_m(w)=Σω_(2j+1)w^j, with ω_j=binom(m,j)(2m-j)!/(2m)!. If b_n=[w^n]1/D_m then the actual targets are Σω_(2j)b_(n-j)>0 and Σω_(2j+1)b_(n-j)>0. A useful new lemma would control negative b-blocks by their preceding positive neighbors with the source numerator weights, uniformly in m,n. For example, derive an all-order recurrence for these two weighted blocks from the displayed q recurrence, rather than falsely requiring b_n≥0. Decisive next calculation: symbolic elimination for the joint state (E_m/D_m,O_m/D_m,E_(m-2)/D_(m-2),O_(m-2)/D_(m-2)) and find a forward-invariant positive cone containing its exact initial vectors. This is a proposed mechanism; no such cone or universal block inequality is established. Enlarging the coefficient sweep will not establish it.
