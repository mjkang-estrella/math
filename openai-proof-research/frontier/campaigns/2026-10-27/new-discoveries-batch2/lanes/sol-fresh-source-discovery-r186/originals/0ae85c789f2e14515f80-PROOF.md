# Schmidlin Conjecture37: proposed full proof

Status: mathematical argument complete; fresh isolated49-declaration12-module strict Lean replay PASS; no independent review, no discovery credit. Exact source arXiv2601.21906v1 (29Jan2026), MathDB372858. Actual definitions on pp3-4, Corollary32 p24-25 and Conjecture37 pp28-29 read; relevant pages rendered and inspected. Domain is x>=0, alpha in[0,1]; extra Dhat condition x+alpha>-1/2 is automatic. Source source2601.21906.pdf SHA256 1cd3cf2811b7019b54a9d6e6b116551dced876d88aa076d72c386a2cd41ebc9d.

## Literal source and stronger conclusion
The source uses Pi(x)=Gamma(x+1), interpolatedPi=Pi(x)*(x+1)^alpha,
S_(1/2)(y)=sqrt(2pi)*exp(-1/2)*(y+1/2)^(y+1/2)*exp(-y),
mhat=log(interpolatedPi/S_(1/2)(x+alpha)). It asks mhat<=1/[12(x+alpha)+18-12exp(1/48)].

Set z=x+1>=1,a=alpha-1/2>=-1/2 and k=12(exp(1/48)-1). Define
R(z)=logGamma(z)-(z-1/2)logz+z-(1/2)log(2pi),
E(z,a)=(z+a)log(1+a/z)-a.
Direct logarithmic algebra yields mhat=R(z)-E(z,a), while the source bound is1/[12(z+a)-k]. We prove a STRICT bound for every alpha>=0, which in particular proves the exact conjecture. No optimality claim.

## Classical ingredient and self-contained certificate route
The classical Stirling remainder estimate is
R(z)<=U(z):=1/(12z)-1/(360z^3)+1/(1260z^5), z>0.
This follows from DLMF5.11.1/5.11(ii) and is wholly uncredited as new mathematics.
For a self-contained Lean proof we instead use recurrence and a finite logarithm estimate:
R(z)-R(z+1)=h(z):=(z+1/2)log(1+1/z)-1.
For v=1/(2z+1) in(0,1), the standard atanh-series remainder gives
h(z)<=v^2/3+v^4/5+v^6/7+v^8/(1-v^2)=:H(z).
(Use Mathlib log_div_le_sum_range_add with n4, multiply by1/v and subtract1.)
Exact rational simplification gives
U(z)-U(z+1)-H(z)=P(z)/[2520z^5(z+1)^5(2z+1)^6],
P(z)=112z^8+448z^7+1295z^6+2317z^5+2200z^4+1061z^3+253z^2+34z+2>0.
Consequently R(z)-U(z) is strictly increasing under z->z+1. Its limit is0, proving R(z)<=U(z).

The limit is independently bridged to actual Gamma using pinned Mathlib Stirling.stirlingSeq and log-Gamma convexity. For integer n>=2 and r in[0,1], BohrMollerup.f_add_nat_le/ge imply
logGamma(n)+r log(n-1)<=logGamma(n+r)<=logGamma(n)+r logn.
Log bounds u/(1+u)<=log(1+u)<=u then give
R(n)-2/(n-1)<=R(n+r)<=R(n)+1/n.
At integers R(n)=log(stirlingSeq n)-(1/2)logpi, tending0. Taking n=floor z proves R(z)->0 as z->infinity. No unproved Gamma asymptotic assumption is left in the completed formal route.

## Entropy and polynomial certificate
For z>0,z+a>0, E>=0, from logt>=1-1/t. If a>=0, log(1+t)>=2t/(2+t) gives the sharper E>=a^2/(2z+a).
Let D=2520z^5(a+2z)(48a+48z-1), positive for z>=1,a>=0. Then
1/[12(z+a)-1/4]-U(z)+a^2/(2z+a)=[A(z)a^3+B(z)a^2+C(z)a+F(z)]/D,
A=120960z^5,
B=120960z^6-2520z^5-10080z^4+336z^2-96,
C=-20160z^5+210z^4+1008z^3-7z^2-288z+2,
F=420z^5+672z^4-14z^3-192z^2+4z.

For t=z-1>=0, B(t+1) has positive coefficients descending
120960,723240,1791720,2353680,1729056,673512,108600.
The discriminant complement 4BF-C^2, evaluated at t+1, has positive coefficients descending
203212800,2149822080,10299502080,29404384380,55375719840,71883106764,65187512040,40869159443,17049349100,4345739674,553547260,16630775.
Thus B>0 and 4BF-C^2>0. The exact identity
4B(Ba^2+Ca+F)=(2Ba+C)^2+(4BF-C^2)
proves the quadratic strictly positive; Aa^3>=0. Therefore
R-E<=U-a^2/(2z+a)<1/[12(z+a)-1/4]<=1/[12(z+a)-k].
Here k>=1/4 follows from expu>=1+u, while k<1/2 follows from expu<=1/(1-u), u=1/48. All denominators are positive.

For -1/2<=a<0, U(z)<=1/(12z), E>=0, and12(z+a)-k<12z; hence directly R-E<1/[12(z+a)-k]. This completes the claimed range, including the full source domain and all its boundaries.

## Novelty scope and honest remaining gates
This is ONE prospective explicit-conjecture resolution, not a new Stirling theorem or entropy theorem. Source Corollary32 already proves x>=1 and receives no separate credit. No worldwide priority claim.
Preliminary screen: latest primary arXiv v1 only; live MathDB empty; OpenAlex workW7126272241 has0 indexedciters; author Basel homepage lists this as sole relevant preprint and no successor. Search results include an AI summary, rejected as prior mathematical evidence. Empty databases are not a priority certificate. Need independent source/math/formal/novelty/eligibility review, manuscript and extracted proof packet before any credit. No MathSciNet/zbMATH/Scopus sweep yet. The classical three-term bound alone does not state the two-variable conjecture; the rational discriminant certificate is the added argument, subject to independent eligibility assessment.
