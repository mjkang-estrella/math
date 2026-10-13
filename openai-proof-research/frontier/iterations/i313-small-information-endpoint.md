# I313 — small-information endpoint: necessary fourth-power loss

2026-10-13. **Parent technical deductions and a new unresolved target.** These deductions are not an additional substantial acceptance. The unrestricted S302 proposal has constants on compact amplitude intervals bounded away from zero; it does not specify their blow-up as information vanishes. Its full proof review remains active and is not assumed below.

Use psi(t)=((1+t)log(1+t)+(1-t)log(1-t))/2, I(u)=E psi(u)-psi(Eu), Delta_r(u)=psi(ra)-I(T_r u), and d_a(u)=min_(i,sign) E|u-sign*aX_i|², with I(u)=psi(a). Fix 0<r0<=r1<1 and 0<a1<1.

## 1. Exact one-coordinate obstruction to a better endpoint rate

Fix m with 0<|m|<1 and r in (0,1). For every sufficiently small a>0 there is a unique small b=b(a)>0 with

    J(m,b)=[psi(m+b)+psi(m-b)]/2-psi(m)=psi(a).

Indeed J is even in b, analytic at zero, and strictly increasing for positive b with |m|+b<1. Put h=1-m². Expanding in b², the analytic inverse gives

    J(m,b)=b²/(2h)+(1+3m²)b⁴/(12h³)+O_m(b⁶),
    b²=h a²-(2/3)m²a⁴+O_m(a⁶).

These follow from psi''(m)=1/h, psi''''(m)=2(1+3m²)/h³ and psi(a)=a²/2+a⁴/12+O(a⁶). The inverse is analytic in a² because the derivative with respect to b² at zero is 1/(2h)>0. All kernels u_a=m+b(a)X are admissible for small enough a, and their information is exact.

Noise gives T_r u_a=m+rb(a)X. Substitution into the same Taylor expansion yields

    Delta_r(u_a)= [r²(1-r²)m²/(3h)] a⁴+O_(m,r)(a⁶),
    d_a(u_a)=m²+(a-b(a))² -> m².

In particular

    lim_(a->0) a⁴ d_a(u_a)/Delta_r(u_a)
       =3(1-m²)/[r²(1-r²)]>0.

No inequality d_a(u)<=C a^(-p) Delta_r(u), with C independent of a, can hold for all admissible kernels when p<4. This already fails in dimension one. An a^(-2) guess based only on balanced diffuse kernels misses the persistent bias. The statement is a lower obstruction, not a proof that exponent four suffices in all dimensions.

## 2. Exponent four suffices at the one-coordinate scope

The completed I131 deduction N131, independently checked within I299, states for a genuine one-coordinate field v=m+bX with J=I(v)>0:

    D(v)-F(J)>=(2/3)m²J²,
    F(psi(t))=t atanh(t).

This is not used as a general n-dimensional production bound. Its secant integration formula P128 is also used only for this one-coordinate flow. Both actual proofs were read in I131 lines 155–166 and I128 lines 140–154; their previous full-chain independent validation is in I299. No truth of the proposed full S302 theorem is needed here.

Let t=-log r, y(s)=I(T_(exp(-s))u), w(s)=psi(a exp(-s)), and R(s)=D(T_(exp(-s))u)-F(y(s)). For K=max_[0,psi(a1)] F'<infinity, P128 gives

    Delta_r(u)=integral_0^t exp(-integral_s^t A(v)dv)R(s)ds,
    2<=A<=K.

Orient b>=0. Convexity gives J(m,b)>=psi(b), hence b<=a. Also J(m,b)<=psi(|m|+b), since each summand is at most that value and psi(m)>=0. Therefore a<=|m|+b, and

    d_a(u)=m²+(a-b)²<=2m².

If Delta>=w(t)/2, then Delta>=r0²a²/4>=r0²m²a⁴/4. Otherwise y(s)>=y(t)>w(t)/2>=r0²a²/4, so N131 and P128 give

    Delta>=m²a⁴ r0⁴(1-r1^K)/(24K).

Thus with

    c=min{r0²/4, r0⁴(1-r1^K)/(24K)}>0,

every one-coordinate kernel with 0<a<=a1 satisfies

    d_a(u)<=(2/c) a^(-4) Delta_r(u).

This includes arbitrary allowed bias and original endpoint values by the positive-time integration limit. If m=0 then b=a and both sides vanish. The same conclusion holds for a kernel depending on one coordinate in a larger cube: all other coordinate choices are farther from u. The order a^(-4) is optimal by Section 1. The proof is a technical extraction of N131, not a new substantial nomination.

## 3. The genuinely unresolved target

For fixed a1,r0,r1 as above, does there exist C depending only on these three numbers such that, for every n>=1, 0<a<=a1, r in [r0,r1] and arbitrary u:{-1,1}^n->[-1,1] with I(u)=psi(a),

    d_a(u)<=C a^(-4) Delta_r(u)?                 (S313)

This is a quantitative small-information endpoint problem. The compact-away-from-zero theorem, even if passed, does not supply its rate. A proof cannot apply N131 to general kernels or remove small face-separation factors in the joining tree. The I131 warning about exactly those operations remains in force. A counterexample to S313, if found, must retain exact information and show a⁴ d_a/Delta unbounded; a failure of one intermediate estimate is insufficient.

The coefficient calculation and one-coordinate sufficiency are complete parent deductions, but have not received a new independent review. No literature-priority claim is made. Thirteen findings remain accepted toward twenty.
