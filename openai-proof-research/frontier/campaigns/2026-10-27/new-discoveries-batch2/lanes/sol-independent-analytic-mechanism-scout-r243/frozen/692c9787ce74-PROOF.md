# Full ordinary bridge for Alzer positivity; no discovery nomination

Target: R. B. Paris, arXiv:2012.01423v1, p2 Eq.(1.4), attributed to H. Alzer: for every integer n>=1 and every real 0<x<pi,

    A_n(x) = sum_(k=1)^n sin(sin(kx))/k > 0.

This is a complete classical bridge, not a proposed substantive new outcome. The strongest objection is decisive: Vietoris' 1958 theorem plus Paris' own Bessel expansion and factorial tail yield the entire result by a short source adaptation. No credit requested. The original 1958 proof was not obtained; the exact classical theorem is read in Kwong's actual body, arXiv:1504.06705v1, Theorem A p2. This is an explicit named classical dependency, not an unproved new lemma or a claim to have inspected the 1958 original. Paris' full relevant Sections2/4, including the endpoint-overlap discussion, were read. His numerical lower-envelope observations need not be assumed.

## Classical dependencies and quantitative replacement

Write s_n(t)=sum_(k=1)^n sin(kt)/k. Vietoris' theorem states that a nonincreasing positive sequence a_k tending to zero with a_(2j-1)>=(2j)/(2j-1)*a_(2j) has all sine partial sums nonnegative on [0,pi]. Take

    a_1=2/3, a_2=1/3, a_k=1/k (k>=3).

This sequence is nonincreasing: 1/3=1/3. The pair inequalities are equalities, including a_1=2a_2. Hence for every n>=2,

    s_n(x) >= (1/3)sin(x)+(1/6)sin(2x)
            = (1/3)sin(x)(1+cos(x)).                   (E)

For n=1, the target is immediate. This proves a fully quantified envelope in place of Paris' experimentally described lowest curves.

Paris Eq.(1.5)/(4.1) gives the absolutely convergent identity

    A_n(x)/2 = sum_(r>=0) J_(2r+1)(1) s_n((2r+1)x).

Absolute convergence for each finite n follows from |s_n|<=H_n and the factorial bounds below. We independently use the safe bound |s_n(t)|<=3, avoiding Paris' experimentally motivated choice of 2 in Eq.(2.2). Reduce by symmetry to 0<t<=pi. Write u=nt. If u<=3 then |s_n(t)|<=nt<=3. If u>3, the classical Fourier identity sum_(k>=1)sin(kt)/k=(pi-t)/2 and Abel summation bound the tail after n by 1/[(n+1)sin(t/2)]<=pi/u. Thus |s_n(t)|<=pi/2+pi/u<5pi/6<3. The tail estimate follows by summation by parts from |sum_(k=a)^b exp(ikt)|<=1/sin(t/2); the Fourier identity follows by taking radial limits in -log(1-z). At multiples of pi the bound is immediate. The alternating Bessel defining series gives

    J_1(1)>=8111/18432>7/16, 0<J_3(1)<=1/48,
    0<J_l(1)<2^(-l)/l! (integer l>=1).

The first estimate truncates after 1/2-1/16+1/384-1/18432; successive terms decrease. Positivity and the upper bound follow by the same alternating-series test.

Let B_m=sum_(r>=m+1)4^(-r)/(2r+1)!. Then the part of A_n/2 after r=m has absolute value at most (3/2)B_m. Successive summands have ratio <=1/[4(2m+4)(2m+5)]<1/2, so

    B_m < U_m := 2/[4^(m+1)(2m+3)!],   m>=1.

In particular B_1<1/1800 (the first summand is 1/1920 and successive ratios are at most 1/168, giving B_1<=7/13360<1/1800). Moreover

    (3/2)U_m < 7/[12(2m+3)^3], m>=1.                       (T)

At m=1 this is 1/640<7/1500. The ratio of U_(m+1)*(2m+5)^3 to U_m*(2m+3)^3 equals

    (2m+5)^2/[4(2m+4)(2m+3)^3] < 1.

The last inequality follows from 2m+5<2(2m+3) and 1<(2m+4)(2m+3). Induction proves (T).

## Central interval

For pi/3<=x<=2pi/3, sin(x)(1+cos(x))>=sqrt(3)/4 (differentiate: cos(x)+cos(2x)<=0 on this interval). By (E), the r=0 term is at least 8111sqrt(3)/221184. The r=1 term is at least -3J_3(1)>=-1/16 and the remaining tail at least -(3/2)B_1. Consequently

    A_n(x)/2 > 8111sqrt(3)/221184 -1/16 -1/1200 >0.

For a rational verification of the strict last sign, sqrt(3)>433/250 and 8111*433/(221184*250)>1/16+1/1200.

## Both endpoint intervals, with no overlap assumption

Put d=min(x,pi-x). Suppose 0<d<=pi/3 and set m=floor((pi/d-1)/2)>=1. Thus

    pi/(2m+3)<d<=pi/(2m+1).

For r=0,...,m, (2r+1)d lies in (0,pi]. Since the multiplier is odd, periodicity reduces (2r+1)x either to (2r+1)d or to pi-(2r+1)d, both in [0,pi]. Vietoris therefore gives s_n((2r+1)x)>=0. Thus all the retained terms beyond the first can be discarded. For 0<d<=pi/2,

    sin(x)(1+cos(x)) >= sin(d)(1-cos(d)) >=4d^3/pi^3.

Here sin(d)>=2d/pi, and 1-cos(d)=2sin(d/2)^2>=2d^2/pi^2. Apply (E) and J_1>=7/16 to obtain

    J_1 s_n(x) >= 7d^3/(12pi^3)
                > 7/[12(2m+3)^3] > (3/2)B_m.

The full expansion now gives A_n(x)>0. This and the central interval cover every 0<x<pi and every n>=2, completing the target.

## Other routes retained and limits

Before the Vietoris bridge was located, a direct boundary route succeeded: q(t)=sin(sin(t))/t is strictly decreasing for 0<t<pi. For t<=pi/2, its derivative numerator is at most u*cos(u)-sin(u)<0, u=sin(t), using t*cos(t)<=sin(t); for t>=pi/2 it is immediately negative. Therefore at x=pi-epsilon with n*epsilon<=pi the alternating terms pair positively. At 0<x<=pi/n all terms are nonnegative and at least the first is positive. These prove genuine n-uniform boundary strips but do not close the middle. They receive no separate credit.

An attempted unweighted-prefix argument fails: at x=5pi/6, sin(sin(x))+sin(sin(2x))=sin(1/2)-sin(sqrt(3)/2)<0. Positivity of Bessel coefficients alone also fails to imply positivity because s_n at dilated arguments can be negative. The quantitative envelope and adaptive factorial tail above are the missing bridge; no finite sweep is used.

The classical dependency is explicit and supplies the substantive objection. Bounded current arXiv queries found the original and related sine-polynomial work; no complete current proof-registry head, all citing bodies, or publisher update was obtained. No priority claim, acceptance claim, Lean endpoint or manuscript is supplied.
