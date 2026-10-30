# Complete source-level proof — candidate credit zero

Claim: for every real0<a<=1/2,
 f_a(t)=|E_(2a,1)(-t)|²+t|E_(2a,1+a)(-t)|²
is C-infinity on t>0 and (-1)^k f_a^(k)(t)>=0 for all natural k.
The Mittag-Leffler symbols mean the literal convergent Gamma-denominator series.
The closed Lean endpoint is MittagModulus.source_conjecture_370772.
This is a mathematical/formal certificate, not novelty or acceptance clearance.

## 1. Genuine series and the cross kernel

For a,b>0, sum z^n/Gamma(an+b) is entire. The certificate proves convergence
by splitting n into arithmetic residue classes with step m*a>=1; Gamma
monotonicity for arguments>=2 and its recurrence give an eventual geometric
ratio bound. No assumed Mittag-Leffler interface is used.
The even/odd split gives E_a(i sqrt(t))=E_(2a,1)(-t)+i sqrt(t)E_(2a,1+a)(-t),
so f_a(t)=|E_a(i sqrt(t))|². The real series expression makes f_a globally smooth.

Let I(x)=integral_0^1 exp(xu²)du. The exact polynomial moments
 B_n=integral_0^1(1-u²)^n du=sqrt(pi)n!/[2Gamma(n+3/2)]
follow from B0=1 and B_(n+1)=2(n+1)/(2n+3) B_n, obtained by integrating the
derivative of u(1-u²)^(n+1). A uniform exp(|x|) majorant permits actual
termwise integration of the exponential series. Consequently
 integral_0^1 exp(-x(1-u²))du=sqrt(pi)/2 E_(1,3/2)(-x),
 E_(1/2,1)(ir)=exp(-r²)[1+2ir/sqrt(pi) I(r²)].
Both identities are proved from the actual series in Lean.
For v,w,t>=0 this gives
 K(v,w,t)=Re[E_(1/2)(i sqrt(vt)) conjugate(E_(1/2)(i sqrt(wt)))]
 =exp(-(v+w)t)[1+4t sqrt(vw)/pi I(vt)I(wt)].

## 2. Positive one-dimensional Laplace formula

For v,w>0, K equals
 J(t)=2sqrt(vw)/pi [integral_0^1 exp(-tw(1-u²))/(v+wu²)du
                   +integral_0^1 exp(-tv(1-u²))/(w+vu²)du].
Here is a complete elementary identification. Integrating the derivative of
u exp(xu²) gives I(x)+2xI'(x)=exp(x). Product differentiation shows that the
right side P of the product formula for K obeys
 P'+(v+w)P=2sqrt(vw)/pi [exp(-wt)I(wt)+exp(-vt)I(vt)].
J obeys exactly the same ODE: parameter differentiation cancels each denominator,
since v+w-w(1-u²)=v+wu², and symmetrically. All integrands and derivatives
are continuous on compact parameter rectangles, so these differentiations
are justified. The certificate proves the compact-domination lemma explicitly.
The initial values are
 J(0)=2/pi[atan(sqrt(w/v))+atan(sqrt(v/w))]=1=P(0).
Thus exp((v+w)t)(P-J) has zero derivative and zero value at0, proving equality.
The two denominators are positive and both rates w(1-u²),v(1-u²) are nonnegative
on[0,1]. For v=0 or w=0, K=exp(-(v+w)t); both zero cases are proved separately.
It follows that all mixed lower differences of K in t>0, with arbitrary
positive steps, are nonnegative, including the zero-scale cases.

## 3. Actual finite normalized averaging

Put beta=2a in(0,1]. For k>=1, define
 T_k g(x)=beta*g(x)+(1-beta)*k*integral_0^1 u^(k-1)g(xu)du.
This is a normalized positive interval operator and a norm contraction on[0,C].
For q>=0, T_k(x^q)=(k+beta*q)/(k+q) x^q, by the actual rpow integral.
Compose k=1..N+1 and evaluate at C_N=N^(1-beta), N>=1; call this functional A_N.
Its exact moments are
 R_N(q)=N^((1-beta)q)*product_(k=1)^(N+1)(k+beta*q)/(k+q).
The index N+1 is intentional and matches the Lean source; the earlier frozen
ordinary proof used N factors, an asymptotically equivalent but different choice.
Euler's Gamma limit gives R_N(q)->Gamma(1+q)/Gamma(1+beta*q).
For d=(1-beta)q>=0,
 R_(N+1)/R_N=((N+1)/N)^d*(N+2+beta*q)/(N+2+q)>=1:
((N+1)/N)^d>=1+d/(N+1), and multiplying out leaves exactly
d(1+beta*q)/(N+1)>=0. Hence R_N(q) is bounded above by its Gamma-ratio limit.

Define M_N(z)=A_N(E_(1/2)(z sqrt(x))). Compact-interval uniform majorants and
the exact moments prove the genuine identity
 M_N(z)=sum_(n>=0) R_N(n/2)/Gamma(1+n/2) z^n.
Each coefficient lies between0 and1/Gamma(1+an), and tends to that bound.
The latter entire series dominates on every bounded z disk, so M_N(z)->E_a(z).
This is proved by actual finite averages, norm bounds and dominated convergence;
no stable-law existence or assumed moment-generating function is needed.
Real linearity and conjugation of the actual integrals give exactly
 |M_N(i sqrt(t))|²=A_N^(v) A_N^(w) K(v,w,t).
All continuous-linear commutations and continuity requirements are proved.

## 4. Mixed differences and all derivative signs

For ell>=0, the mixed lower difference of exp(-ell*t), at steps h1,...,hk>0,
is exp(-ell*t)*product_j(1-exp(-ell*hj))>=0. This property is preserved by
positive scalar sums and the actual interval averages. Section2 therefore
makes it hold for every actual squared approximant |M_N(i sqrt(t))|².
Their pointwise limit is the literal f_a(t), so every finite mixed difference
has the same nonnegative sign at t>0. Finally f_a is C-infinity. All of its
mixed differences are antitone (append the positive step y-x), so their
negative derivatives are nonnegative. Derivation commutes with finite shifts
and differences. Induction applied to -deriv f gives all alternating derivative
signs, including k=0. This is a proved criterion in Lean, not an assumed
Bernstein-representation theorem. The exact source conclusion follows.

## Status and boundaries

Fresh source-only strict replay17modules155declarations PASS, standard3 only;
root read all actual types/axiom reports. Independent final review of these bytes,
actual VoR source comparison, bounded prior-art/substantive adjudication and the
final extracted packet are separate gates. The prior preliminary mathPASS reviewed
the original angular/polar proof; it did not review this newer rational-Laplace
certificate or manuscript. No first-priority claim, no other PDE/zero conjecture,
no auxiliary/helper discovery credit. Candidate0; batch2 stays2/30.
