# Uncredited elementary bridges for the mean candidate

These are root ordinary deductions, not Lean or independent review claims.
They supplement, without changing, the frozen displayed-conjecture proof.

## A positivity without an infinite series

Let d=sqrt17 and a=(5/d-1)/4>0. The literal A in the frozen proof satisfies

    A(t)=a[cosh((d+1)t)-cosh((d-1)t)]
         +(1/2)[cosh(4t)-cosh((d-1)t)].

This follows from the sum/difference identities for hyperbolic products;
the negative coefficient is a+1/2=(5/d+1)/4. Since 4<d<5, all arguments are
positive for t>0 and both bracketed differences are strictly positive. Hence
A(t)>0 immediately from strict increase of cosh on the positive half-line.
No Taylor-series sign theorem is needed.

Equivalently, putting beta=(5-d)/2,

    A(t)=((5-d)/(2d))sinh(dt)sinh(t)
          +sinh(((d+3)/2)t)sinh(beta*t).

From sinh(ct)/t -> c, this gives A(t)/t² -> 2. The coefficient identity is
(5-d)/2+(d+3)(5-d)/4=(25-d²)/4=2. For
B(t)=sinh(t)sinh(alpha*t)sinh(beta*t), alpha=(5+d)/2,
B(t)/t³ -> alpha*beta=2. Thus J(t)=sqrt2 B(t)/((1+2t²)A(t)) ->0 at0+
by finite product/quotient limits. Again no infinite series is required.

## A stronger elementary sandwich

For all distinct positive a,b,

    B_(1/2)(a,b) < M2(a,b) < B_2(a,b).

By symmetry and homogeneity it is enough to take (a,b)=(e^-t,e^t), t>0.
Write m(t)=sqrt2*sinh(t)/atan(sqrt2*t).

For the upper bound set C=cosh(2t)=1+2sinh²t and
w(t)=sqrt2*sinh(t)/sqrt(C). Direct differentiation gives

    w'(t)=sqrt2*cosh(t)/C^(3/2)
          < sqrt2/C < sqrt2/(1+2t²), t>0,

using cosh²t=1+sinh²t<C and sinh(t)>t. Since w(0)=atan(0)=0, integration
gives w(t)<atan(sqrt2*t), equivalently m(t)<sqrt(cosh(2t))=B_2(e^-t,e^t).

For the lower bound, B_(1/2)(e^-t,e^t)=cosh²(t/2). The desired inequality is

    atan(sqrt2*t) < 2sqrt2*tanh(t/2).

On 0<t<=2, convexity of sinh and sinh(1)<2 give
sinh(t/2) <= (t/2)sinh(1) < t. Therefore
cosh²(t/2)<1+t²<1+2t², and the derivative of the right side minus the left
side equals sqrt2[sech²(t/2)-1/(1+2t²)]>0. Its value at0 is zero.

For t>=2, tanh(t/2)>=tanh1>3/4, since e²>7. Hence
2sqrt2*tanh(t/2)>(3/2)sqrt2>2>pi/2>atan(sqrt2*t).
The numerical-looking constants are exact: e<3 implies sinh1<3/2<2;
the exponential series through degree4 at2 sums to7 and its positive tail
gives e²>7; pi<4 is classical. No decimal calculation is used.

Finally beta=(5-d)/2 lies in (0,1/2), d>2, and alpha=(5+d)/2>2.
Strict monotonicity of power means therefore gives

    B_beta < B_(1/2) < M2 < B_2 < B_d,
    B_(-d) < B_(1/2) < M2 < B_2 < B_alpha.

Thus M2 is between Bp and Bq on both branches. Combined with the already
proved strict resultant inequality, this also justifies the source's stronger
super-stabilizability terminology. The sandwich is an auxiliary statement,
not another prospective outcome or a novelty claim. Formal implementation
and independent checking remain necessary before manuscript use.
