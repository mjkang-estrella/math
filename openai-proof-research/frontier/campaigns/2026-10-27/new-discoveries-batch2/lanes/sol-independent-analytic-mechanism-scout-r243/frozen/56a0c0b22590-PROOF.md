# Smooth positive counterexample to Auconi's information-response inequality

Provisional ordinary-math resolution, not an acceptance or priority claim. One family only.

## Literal target and source

Andrea Auconi, *Conjecture of an information-response inequality*, arXiv:2308.09638v2, https://arxiv.org/pdf/2308.09638v2 , submitted18Aug2023, updated20Sep2023. Actual PDF p1 Eq(2) conjectures

    gamma_(X->Y) <= 1-exp(-2I(X;Y))

for the arbitrary smooth input density and fixed smooth channel introduced on that page. Eq(1) defines gamma through the squared conditional input score divided by input Fisher information. Supplement pp1–2 (PDFpp4–5), Eqs(2)–(6), prove its equivalence to the infinitesimal KL-divergence ratio under translation of the input density. No Gaussian-input, symmetry, or Gaussian-channel restriction is imposed on Eq(2). The Gaussian equality case and the Gaussian-small-noise large-information limit on p2 do not claim the general result. We refute the universal inequality inside its positive C-infinity, finite-information setting. We do not refute either restricted theorem.

## Construction

For x in R set t(x)=exp(x)/(1+exp(x)),

    p(x)=2 exp(x)/(1+exp(x))^3,
    s(x)=p'(x)/p(x)=1-3t(x),    a=1/100,
    P(x,y)=p(x)p(y)[1+a s(x)s(y)].

The change of variables t=t(x) gives p(x)dx=2(1-t)dt on (0,1). Thus p is a probability density, is smooth and everywhere positive, and -2<s<1. Write M_j=integral p s^j. Direct integration gives

    M0=1, M1=0, M2=1/2, M3=-1/5, M4=3/5.

Indeed M_j=sum_(i=0)^j binom(j,i)(-3)^i 2/((i+1)(i+2)). These are exact rational identities. The joint multiplier lies strictly between .98 and1.04 since -2<s(x)s(y)<4. Consequently P is smooth and everywhere positive. Integrating either coordinate gives the marginal p; its fixed channel is

    K(y|x)=p(y)[1+a s(x)s(y)].

This is normalized and positive for every x. The score s and all its derivatives are bounded, p has exponential tails, its Fisher information J=M2=1/2, and the likelihood ratio P/(p tensor p) is bounded away from zero and infinity. All information integrals used below are finite.

## Exact response

Conditional expectation under the actual joint density is

    E[s(X)|Y=y]=a M2 s(y).

It follows from the source Eq(1) that

    gamma = integral p(y)(a M2 s(y))^2 dy / M2
          = a^2 M2^2 = 1/40000.

This is an equality, not an estimated response.

## Certified information bound

Let X0,Y0 be INDEPENDENT with density p, W=s(X0)s(Y0), and z=aW. Then

    I=E0[(1+z)log(1+z)],  E0 z=0,
    E0 z^2=a^2/4,  E0 z^3=a^3/25,  E0 z^4=9a^4/25,
    |z|<4a=1/25.

For |z|<1 the absolutely convergent identity is

    (1+z)log(1+z)=z+sum_(k>=2) (-1)^k z^k/[k(k-1)].

For k>=4, k(k-1)>=12. Uniform convergence on |z|<=1/25 justifies termwise expectation, and gives

    |I - (a^2/8-a^3/150)|
       <= E0|z|^4/[12(1-4a)]
       = 1/3200000000.

The difference between gamma/2 and this upper bound is exactly

    a^3/150 - 1/3200000000 = 61/9600000000 >0.

Therefore 2I <= gamma -61/4800000000 < gamma. Finally 1-exp(-u)<=u for u>=0, applied to the nonnegative relative entropy u=2I, yields

    1-exp(-2I) <= 2I < gamma.

This is a complete counterexample to the source's universal Eq(2). No floating-point calculation, finite optimization or unproved quantified lemma is needed.

## Independent route through the actual perturbation definition

Keep K fixed and translate only the input to q_h(x)=p(x-h). Its output is exactly

    q_h^Y(y)=p(y)[1+a c(h)s(y)],
    c(h)=integral p(x-h)s(x) dx.

Here c(0)=0 and c'(0)=-integral p'(x)s(x)dx=-M2. Differentiation is justified by exponential tails and bounded s; translations in a fixed compact h-interval have a common integrable envelope. Thus c(h)=-h M2+O(h^2). The same uniformly convergent entropy series gives

    D(q_h^Y || p)=a^2 h^2 M2^3/2+O(h^3).

For the input, log p has bounded derivatives of order>=1, with first and second derivatives s and s'. With U distributed according to p,

    D(q_h||p)=E[log p(U)-log p(U+h)]
            =-h E s(U)-h^2 E s'(U)/2+O(h^3)
            =h^2 M2/2+O(h^3).

The integration-by-parts identity E s'=-M2 has vanishing boundary p s. Taking the ratio gives a^2 M2^2, independently matching the source-score route. This also checks that channel-versus-joint perturbation conventions have not been confused.

## General mechanism and unsuccessful routes retained

For any positive density with bounded score s of mean0, variance J>0 and nonzero third moment m3, the same rank-one channel gives gamma=a^2 J^2 and

    I=a^2 J^2/2-a^3 m3^2/6+O(a^4).

Hence gamma-2I=a^3 m3^2/3+O(a^4)>0 for sufficiently small positive a. The explicit density above removes all unspecified constants. The key is aligning the channel perturbation with the input SCORE while keeping nonzero score skewness. The symmetric-score route has m3=0 and does not provide this cubic sign; an arbitrary bounded test function loses leading-order equality by Cauchy–Schwarz. Those shortcuts are not asserted to work. A preliminary loose fourth-moment bound |W|<=4 would be too coarse at a=1/1000 (remainder about2.14e-11 versus cubic improvement6.67e-12); using the exact fourth moment fixes this, and the final witness uses a=1/100.

## Strongest substantive classical-adaptation objection

The joint density p(x)p(y)(1+a f(x)g(y)) is a classical Sarmanov/Lancaster construction, not a new probability model. The log-series for relative entropy and the score conditional-expectation identity are also classical; the source itself proves the last identity. Angulo–Ruiz-Medina2212.12209v1 Section2.1 Eq(1) p4 and Section3.1 Eq(9) p8 exhibit Lancaster-Sarmanov densities and their exact mutual-information functional. Their Theorem1/proof pp10–11 concerns large-distance asymptotic orders for subordinated random fields, not a bound between translation-score response and mutual information, and does not state this counterexample. Nonetheless the FULL adaptation is short: choose bounded skew score, align rank-one kernel with it, retain the cubic entropy term, and dominate the remainder. A specialist might regard precisely this bridge as routine; no proof-length argument dismisses that objection. Root must adjudicate substantive credit independently. Classical construction, moments, weak-dependence expansion, general mechanism and explicit a are ONE family, never extra discoveries.

Barnes–Ozgur2102.05802v2 Theorem1 and proof pp2–3 give I_Y<=2N^2 I(X;Y) for an N-sub-Gaussian score, not I_Y/J<=1-exp(-2I). Here the score's third moment is nonzero. It cannot be sub-Gaussian with N^2=J: expanding log E exp(ts)=Jt^2/2+m3 t^3/6+O(t^4) violates that bound for one sign of small t. The legitimate larger sub-Gaussian proxy leaves slack and is not contradicted. Auconi's Gaussian-input thermodynamic application and Gaussian-small-noise asymptotic proof remain intact.

Bounded current arXiv author/topic searches and immutable history found no matching resolution; neither complete current proof registries nor exhaustive citing/journal bodies were accessible. This is not certified worldwide novelty. No Lean, manuscript or external mutation is included.
