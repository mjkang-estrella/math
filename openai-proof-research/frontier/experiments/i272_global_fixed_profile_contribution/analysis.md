# I272 independent contribution analysis

Date: 2026-10-12. Verdict: **TECHNICAL**, contribution only. Target I271 SHA256 `a3ecaddeec1745579ca729e7d2d1e9067c9d97006169a1df0eedfa1361fb54fa`. All OpenAI results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. This is analytic review, with no research code, tests, numerical scans or new nomination.

## Exact scope and preserved decisions

Fix a>0, 1/2<gamma<3/2, r=1/(gamma-1/2)>1. The profile is w=(r+1)a² sech²(ra x), with normalized phi=c sech^(1/r)(ra x). For every finite m>=2 and every measurable REAL unit v, put P=vv^T, H=-d² I_m-wP, J=inf over real unit e of integral w phi²[1-(v.e)²], and D=a^(2gamma)-Tr H_-^gamma. I271 claims cJ<=D<=CJ without initial smallness, with constants depending only on a,gamma. It fixes profile, scale and center. The m=1 case is trivially constant-projector equality; no additional channel scope is inferred.

I265 PASS validates the I264 local statement and its particular tau,c_local,M_gamma. It does not pass I271. I266 TECHNICAL is retained for I264. I266 already proves the GLOBAL delta-versus-J estimate below, but its tail absorption needs J small. It does not prove D small implies J small. I271 supplies that genuinely missing implication. Treating its theorem as the already reviewed local scope would be wrong.

## Independent check of the exponent argument

For q=s-1/2 in (0,1/r), beta integration gives

    integral w^(q+1)
      =(r+1)^(q+1) a^(2q+1) sqrt(pi) Gamma(q+1)/[r Gamma(q+3/2)].

Multiplication by the actual sharp C_s cancels both Gamma factors and sqrt(pi):

    B_s/a^(2s)= (r+1)^(q+1) q^q/[r(q+1)^(q+1)].

Write F(s) as the logarithm. Its derivative is log((r+1)q/(q+1)); its second derivative is 1/[q(q+1)]. At q=1/r its value and derivative vanish. On q in [1/(2r),1/r], F''<=4r²/(2r+1). The integral Taylor remainder therefore gives F(gamma-h)<=2r² h²/(2r+1), with no missing factor 1/2.

Order H>=h_scalar I_m>=-a² gives delta=inf spec H+a² in [0,a²], d=delta/a² in [0,1]. If d<1, the lowest negative binding is E1=a²(1-d), and every binding E_j<=E1. Thus

    sum E_j^gamma <= E1^(gamma-s) sum E_j^s <= E1^(gamma-s) B_s.

All s are admissible for wP because tr(wP)^(s+1/2)=w^(s+1/2) is integrable; there is no requirement that w optimize the inequality at s. No matrix or eigenvalue count enters. Taking h=d/(2r) places s strictly above 1/2. Then

    log(sum E_j^gamma/a^(2gamma))
      <= h log(1-d)+F(gamma-h)
      <= -d²/(2r)+d²/[2(2r+1)]
      = -(r+1)d²/[2r(2r+1)].

This checks I271's k0. If the sum is zero, use the direct inequality instead of a logarithm. If d=1 there is no negative spectrum, so D=a^(2gamma). If d=0, use D>=0. Concavity of t -> 1-exp(-k0 t) for t in [0,1] gives exactly D>=a^(2gamma)(1-exp(-k0))d². These are sufficient mechanism checks, not a full proof verdict on every candidate step.

## Exact optimization: a simpler global comparison

The lower-exponent comparison can be minimized explicitly, rather than choosing h and estimating a remainder. Let b=1-d in (0,1), q0=1/r, and

    T(q)=b^(q0-q) (r+1)^(q+1) q^q/[r(q+1)^(q+1)].

The derivative of log T is log((r+1)q/[(q+1)b]) and the second derivative is positive. Its unique minimizer is

    q*=b/(r+1-b)=(1-d)/(r+d),
    s*=1/2+q*,   1/2<s*<gamma.

At that point, (r+1)q*/(q*+1)=b and (r+1)/(r(q*+1))=(r+d)/r. Consequently

    Tr H_-^gamma/a^(2gamma)
        <= (1+d/r)(1-d)^(1/r) =: T_*(d).             (A)

This is the exact minimum of the available upper bounds, NOT a sharp stability constant or an attainability assertion. It uses no new spectral theorem or orientation lemma. For d=0 take the continuous limit; d=1 is handled spectrally as above.

For 0<=d<1,

    log T_*(d)=log(1+d/r)+(1/r)log(1-d)
       <= d/r+(-d-d²/2)/r = -d²/(2r).

Therefore a simpler sufficient comparison is

    D>=a^(2gamma)[1-exp(-d²/(2r))]
      >=a^(2gamma) k_* d²,
    k_*=1-exp(-1/(2r))>0.                            (B)

This improves the displayed quadratic coefficient in I271 but does not alter its statement or files. It is a reviewer calculation for assessing how much mathematical burden remains after the stipulated sharp family. In particular the calculation is not nominated as another finding.

## Ground energy versus orientation, checked globally

For normalized real vector u in H¹, decompose componentwise u=phi b+xi, integral phi xi=0. Then |b|²+||xi||²=1. Set E=sum q_(h_scalar+a²)[xi_i]>=a²||xi||², F_u=integral w|(I-P)u|², R=E+F_u=q_(H+a²)[u]. The covariance definition gives J|b|²<=integral w phi²|(I-P)b|². Minkowski and w<=(r+1)a² yield

    sqrt(J)|b|<=sqrt(F_u)+sqrt(r+1)sqrt(E),
    J|b|²<=(r+2)R.

Using |b|²>=1-R/a² and rearranging, without assuming the right side is positive, gives R>=J/(r+2+J/a²). Test phi e for the upper bound. Hence

    J/(r+2+J/a²)<=delta<=J.                          (C)

Real trial functions suffice for the real operator. Equivalently split complex trials into real and imaginary parts; the real symmetric covariance has the same top eigenvalue on complex vectors. This does not extend the orientation hypothesis to complex v.

The normalized beta-integral ratio is

    Z=integral w phi²=2(r+1)a²/(r+2), 0<=J<=Z.

With B=r+2+2(r+1)/(r+2), (B)--(C) imply

    D>=A_* J²,  A_*=k_* a^(2gamma-4)/B².             (D)

The units are consistent: J scales as a², D as a^(2gamma). If J>=epsilon>0, (D) gives a positive gap A_*epsilon² uniformly over all finite m and all measurable orientations. No compactness of an orientation class is invoked. This specifically rules out compensating for a ground-energy loss by creating many other bindings while the FULL moment approaches equality.

## Promotion and analytic pressure cases

At J<=tau, use exactly the independently validated I264 lemma: D>=c_local J. At J>tau, (D) gives D>=A_*tau J. Thus min(c_local,A_*tau) is a global lower coefficient. For J<=a²/8, (C) and the same mean-value derivative bound give D<=M_gamma J, after discarding the other nonnegative moments. For J>a²/8, D<=a^(2gamma)<8a^(2gamma-2)J. The upper comparison therefore needs no new global mechanism.

Constant-projector fields, including arbitrary measurable sign changes, give J=D=0. Orthogonal indicator defects, rapidly oscillating fields and arbitrarily many finite channels require no modification of (A)--(D). The previously analyzed shrinking-core and translated-tail examples remain inside the validated local lemma whenever their J tends to zero. Away from that neighborhood the new scalar envelope, rather than the old local tail estimate, applies. Large m or high oscillation cannot enter its constants because the only spectral input is a dimension-independent sum bound and E_j<=E1.

A single nonsharp lower-exponent theorem is insufficient: if its cost is larger than a^(2s) by a fixed factor at the target exponent, its logarithmic upper bound has a positive intercept and does not force a ground binding close to a² as D tends to zero. The sharp family and the tangency of THIS fixed soliton cost are essential. Likewise D>=0 and strict equality alone give no uniform quantitative gap over this noncompact class. These limitations are not hidden by calling the method classical.

## Contribution conclusion and boundary

The new implication is real and useful, and the dimension-independent estimate is stronger evidence than an unsupported compactness slogan. The reason for TECHNICAL is the positive complete reduction of the added scope: all nonlinear orientation geometry was already handled globally in I266; the only new passage is the elementary moment ceiling optimized against an explicit scalar sharp-constant family, with exact value (A); the final linear bound is the usual local estimate plus a positive gap outside its radius. The global adjective and the brevity of the proof are neither sufficient reasons for acceptance nor sufficient reasons for rejection. Here the fixed profile makes the outside-neighborhood obstruction fully encoded in one known scalar function.

No primary theorem read literally states I271's physical J/full-moment estimate; KNOWN is unwarranted. No unresolved mechanism issue was found that requires UNRESOLVED at the contribution gate. The verdict does not declare I271 proof PASS, optimal constants, or exhaustive priority. A meaningful presentation repair is to state this as an explicit global fixed-profile corollary, credit I266 for (C), and expose (A) rather than emphasize a Taylor choice as a new stability theory.

A substantive separating extension would have to survive loss of the fixed profile, where tr W^(s+1/2) varies and the tangent scalar function is no longer available, or resolve interacting occupied channels, scales or centers. Those are possible future directions, not extra hypotheses demanded of I271 and not the sole reason for this verdict. I272 does not author such an extension, modify a candidate, change counts, or appeal the previous decisions.
