# Proposed exact midpoint refutation — eligibility NOT presumed

Target: Baricz–Bhayo–Vuorinen1305.0938v2 Conjecture1, published Filomat29:2(2015) Conjecture2.4, MathDB325512. Literal assertion: for EVERY fixed x in(0,1), F(p,x)=integral_0^x (1+t^p)^(-1/p)dt is strictly concave for ALL p>0.

Proposed counterexample: x=1/4096, endpoints p0=1/12,p2=1/4, midpoint p1=1/6. All parameters are positive interior points. The separate p>1 Turan assertion is NOT refuted. The p-Laplacian motivation usually uses p>1; the2019 survey restates concavity on(1,infinity). This may make the result a mere parameter-domain correction under the campaign standard; an independent reviewer must decide before any formal investment or credit. No discovery claimed.

For an integer N>0 and r>=0, substitution t=u^N yields
 F(1/N,r^N)=N integral_0^r u^(N-1)/(1+u)^N du.
For N4,r1/8 and N6,r1/4 the endpoint is the same x=1/4096.

Let P3(u)=1-4u+10u^2-20u^3 and
 P6(u)=1-6u+21u^2-56u^3+126u^4-252u^5+462u^6.
Exact identities:
 1-(1+u)^4P3=u^4(35+84u+70u^2+20u^3)>=0,
 (1+u)^6P6-1=u^7(792+3465u+6160u^2+5544u^3+2520u^4+462u^5)>=0.
Thus, for u>=0, P3<=(1+u)^(-4) and (1+u)^(-6)<=P6.
Multiply by4u^3 or6u^5 and integrate over the stated positive intervals:
 F(1/4,x)>=4 integral_0^(1/8) u^3 P3du=2291/13762560=L,
 F(1/6,x)<=6 integral_0^(1/4) u^5 P6du=1574453/19377684480=U.
Exact rational gap L-2U=38411/9688842240>0.
Since F(1/12,x)>=0, this proves
 (F(1/12,x)+F(1/4,x))/2-F(1/6,x)>=38411/19377684480>0,
contradicting even non-strict concavity at that midpoint.

Independent60digit quadrature gives midpoint gap about7.727961189e-6, greater than the proved lower bound about1.982e-6. Numeric values are sanity evidence only; the polynomial identities, substitution and rational integrals are the proof.

Scope: one proposed refutation of the literal positive-p concavity assertion only, not all related conjectures. No Lean endpoint, paper, accepted novelty, general concavity threshold or discovery count. Source/search/citing-body and substantive-eligibility gates remain. Direct parameter0 flatness also suggests a simple asymptotic contradiction, so mere ease of a witness does NOT establish substantive eligibility.
