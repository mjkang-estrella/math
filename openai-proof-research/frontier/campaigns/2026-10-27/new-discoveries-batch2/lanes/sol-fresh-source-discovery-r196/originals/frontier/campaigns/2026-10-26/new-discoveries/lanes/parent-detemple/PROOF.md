# A proposed refutation of the DeTemple complete-monotonicity threshold

Credit **0**. Full mathematical argument below; no Lean endpoint or manuscript
yet. Prior-art and substantive-eligibility review are pending. This concerns
Conjecture 1(ii), not the ratio monotonicity in Conjecture 1(i).

## Exact source

Yang, arXiv:1409.6411, equation (3.3) p.12 and Conjecture 1(ii) p.14.
The published successor is Yang–Chu–Zhang, *Necessary and sufficient conditions
for functions involving the psi function to be completely monotonic*, J. Inequal.
Appl. 2015:157, DOI 10.1186/s13660-015-0674-8. Its equation (3.3) and Conjecture
1(ii), p.15, have the identical definitions and claim. The publisher's actual
HTML body and PDF were obtained, not merely its abstract.

For x>0 set R(x)=psi(x+1/2)-log(x), where psi=Gamma'/Gamma, and

    P_a(x)=x^4+a*x^2+7*a/40-31/336,
    G_a(x)=24*P_a(x)*R(x)-(x^2-7/40+a).

The conjecture says that -G_a is completely monotone on (0,infinity) iff
a<=155/294. All signs and the parentheses in (3.3) matter.

## Explicit strictly interior counterexample

Take a=527/1000 and x=1/50. These satisfy

    155/294-a=31/147000>0,  x>0.

At this point z=x+1/2=13/25, and exact arithmetic gives

    P_a(x)=91379/525000000>0,
    P_a'(x)=2639/125000>0,
    P_a''(x)=2647/2500>0.

Use the following classical elementary estimates, justified below:

    psi(z)>-31/15,  psi'(z)>0,  psi''(z)>=-20,
    log(50)>15/4.

Consequently R(x)>101/60, R'(x)>=-50 and R''(x)>=2480. Product differentiation,
with every coefficient multiplying these bounds positive, gives

    G_a''(x)=24*P_a''(x)*R(x)+48*P_a'(x)*R'(x)
             +24*P_a(x)*R''(x)-2
             > 24*(2647/2500)*(101/60)
               -48*(2639/125000)*50
               +24*(91379/525000000)*2480-2
             =510221/1093750>0.

Thus (-G_a)''(1/50)<-510221/1093750<0. Complete monotonicity requires the second
derivative nonnegative at every positive argument, so the conjectured sufficient
condition fails even for a strictly interior positive parameter. No limiting
argument, endpoint interpretation, or typo correction is needed for this witness.

## Proof of the scalar estimates

The standard convergent polygamma series for z>0 are

    psi'(z)=sum_{n>=0}(n+z)^(-2)>0,
    psi''(z)=-2*sum_{n>=0}(n+z)^(-3).

For z>=1/2, comparison of the decreasing cubic reciprocal with its integral gives

    sum_{n>=0}(n+z)^(-3)
      <=sum_{n>=0}(n+1/2)^(-3)
      <=8+integral_0^infinity(t+1/2)^(-3)dt=10.

Hence psi''(z)>=-20. Positivity of psi' gives
psi(z)>=psi(1/2)=-gamma-2*log(2)>-2/3-7/5=-31/15.
Here gamma<2/3 is the classical harmonic/log bound (also present in pinned
Mathlib as Real.eulerMascheroniConstant_lt_two_thirds). For completeness,
the logarithm bounds follow from the convergent series

    log((1+u)/(1-u))=2*sum_{k>=0}u^(2*k+1)/(2*k+1), 0<u<1.

At u=1/3 its first two terms and geometric tail give
log(2)<56/81+1/540=1123/1620<7/10. Its first term gives log(2)>2/3.
At u=2/3 its first three terms give log(5)>1924/1215. Therefore

    log(50)=log(2)+2*log(5)>4658/1215>15/4.

All omitted log-series terms are positive; the displayed tail estimate uses
1/(2*k+1)<=1/5 for k>=2.

## Independent qualitative mechanism and formalization route

At a0=155/294, 7*a0/40-31/336=0. If h(x)=psi(x+1/2), h is analytic near zero.
Differentiating the exact formula at positive x gives

    G_a0''(x)=24*[(12*x^2+2*a0)*h(x)
                    +(8*x^3+4*a0*x)*h'(x)
                    +(x^4+a0*x^2)*h''(x)
                    -(12*x^2+2*a0)*log(x)-7*x^2-3*a0]-2.

Every term except the negative logarithm has a finite limit at zero, so
G_a0''(x) tends to +infinity as x tends to 0 from the right. Continuity in a
then produces failures with a<a0 as well. This is a second rigorous proof
of interior failure, although the rational point above is the explicit witness.

A Lean alternative avoiding new quantitative polygamma series is to use finite
differences. Let D(x)=G_a0(3*x)-2*G_a0(2*x)+G_a0(x). Exactly,

    D(x)/x^2 =24*[(81*x^2+9*a0)*h(3*x)
                     -2*(16*x^2+4*a0)*h(2*x)+(x^2+a0)*h(x)
                     -(50*x^2+2*a0)*log(x)
                     -(81*x^2+9*a0)*log(3)
                     +2*(16*x^2+4*a0)*log(2)]-2.

Continuity of h alone implies this tends to +infinity. Thus -G_a0 fails midpoint
convexity at three strictly positive points. Its finite-difference expression is
continuous in a, yielding a strictly interior a<a0 with the same failure.
Complete monotonicity implies convexity by the ordinary second-derivative
criterion. Pinned Mathlib defines Complex.digamma as logDeriv Gamma; its local
analyticity at 1/2 follows from Gamma analyticity and nonvanishing. This route
would prove a closed literal source refutation with an existential strictly
interior witness, without assuming a surrogate digamma or unproved source bridge.

## Novelty and limitations

No prior resolution has been found in the initial targeted searches. This is
not a novelty PASS. OpenAlex identifies fourteen citing works of the published
source; all require review, especially the author's later gamma and Laplace
papers. The 2018 Laplace-ratio paper's actual harmonic-number section concerns
1/R-24*x^2 and does not itself state this G_a refutation. Searches of public
proof repositories, companions, citations and other indexed sources remain
necessary. No worldwide-priority or exact sharp replacement threshold is claimed.

The exact rational checker certifies the arithmetic and identities only. Its
mpmath output is a numerical cross-check, not the justification of the psi bounds.
Standard polygamma and logarithm facts are credited ingredients, not discoveries.
