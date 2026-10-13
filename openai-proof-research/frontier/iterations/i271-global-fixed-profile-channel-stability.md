# I271: global fixed-profile channel stability

Parent derivation, 2026-10-12. **New unreviewed scope; no accepted-count change.** I264's weighted-neighborhood estimate passed the I265 proof gate but was judged TECHNICAL in I266. This note keeps one spectral chain and removes the weighted-neighborhood hypothesis. It does not overturn that prior contribution verdict or count another finding.

## Statement

Fix a>0, 1/2<gamma<3/2 and r=(gamma-1/2)^(-1)>1. Let

    w=(r+1)a^2 sech^2(ra x), phi=c sech^(1/r)(ra x), integral phi^2=1,
    P=v v^T, H=-d^2 I_m-wP,
    J=inf_(real |e|=1) integral w phi^2[1-(v dot e)^2],
    D=C_gamma integral w^(gamma+1/2)-Tr(H)_-^gamma.

For EVERY finite m>=2 and EVERY measurable real unit field v, without any initial closeness, amplitude, support, variation or derivative assumption, the proposed theorem is

    c_global J<=D<=C_global J,                         (G)

with positive explicit constants depending only on a,gamma. In particular small full spectral deficit implies closeness to one constant rank-one channel with the fixed scalar soliton profile, uniformly in m.

The scalar profile, scale and center remain fixed. Arbitrary matrix potentials, variable profiles, several occupied solitons, complex orientation fields, endpoint exponents and infinite-dimensional channels are not claimed. This is global in orientations, not global on the whole matrix optimizer manifold.

## 1. A global quadratic bound by changing the exponent

Write lambda1=inf spec(H)=-a^2+delta and d=delta/a^2. Since 0<=wP<=w I, H>=h I>=-a^2, while its essential spectrum starts at zero. Thus 0<=d<=1. If there is no negative spectrum, d=1 and D=a^(2gamma), and the desired quadratic bound below is immediate. Otherwise all negative binding energies E_j satisfy 0<E_j<=E_1=a^2(1-d).

For an exponent s in (1/2,gamma), the stipulated matrix inequality gives

    sum_j E_j^gamma <=[a^2(1-d)]^(gamma-s) B_s,
    B_s=C_s integral w^(s+1/2).

This use of a different exponent is permitted: the matrix theorem covers every positive matrix potential with the relevant finite integral; wP satisfies each exponent's hypotheses. The target-gamma soliton need not optimize the s inequality.

Put q=s-1/2. The exact beta integral and the stipulated C_s yield

    B_s/a^(2s)=[(r+1)^(q+1)/r] q^q/(q+1)^(q+1).

Let F(s)=log(B_s/a^(2s)). At s=gamma, q=1/r, direct differentiation gives

    F(gamma)=F'(gamma)=0,
    F''(s)=1/[q(q+1)].

For s in [gamma-1/(2r),gamma], q>=1/(2r), so

    0<=F(s)<=[2r^2/(2r+1)](gamma-s)^2.               (1)

For 0<d<1 choose h=d/(2r) and s=gamma-h. This lies strictly between 1/2 and gamma. Combining (1) with log(1-d)<=-d gives

    log[(sum_j E_j^gamma)/a^(2gamma)]
       <=h log(1-d)+F(gamma-h)
       <=-d^2/(2r)+d^2/[2(2r+1)]
       =-k0 d^2,
    k0=(r+1)/[2r(2r+1)]>0.                          (2)

If the sum is zero, the same inequality is interpreted directly without taking its logarithm. The endpoint d=0 follows by nonnegativity of the deficit. Since C_gamma integral w^(gamma+1/2)=a^(2gamma), (2) implies

    D>=a^(2gamma)(1-exp(-k0 d^2))
      >=a^(2gamma) k1 d^2,
    k1=1-exp(-k0)>0.                                (3)

The final step uses concavity of 1-exp(-k0 t) on 0<=t<=1. Thus a small deficit forces the lowest eigenvalue close to -a^2, with no compactness or dimension-dependent passage.

## 2. Global ground energy controls orientation

Here is the elementary global comparison also derived in the I266 contribution review. For any normalized vector u write

    u=phi b+xi, integral phi xi=0,
    |b|^2+||xi||_2^2=1.

The scalar gap gives

    E=sum_i q_(h+a^2)[xi_i]>=a^2||xi||_2^2,
    F_u=integral w |(I-P)u|^2>=0,
    R_u=q_(H+a^2)[u]=E+F_u.

The definition of J and the triangle inequality imply

    sqrt(J)|b|<=sqrt(F_u)+sqrt(r+1)sqrt(E),
    J|b|^2<=(r+2)R_u.

Together with |b|^2>=1-R_u/a^2, this gives

    R_u>=J/(r+2+J/a^2).

Taking the variational infimum, and separately testing phi e for an optimal constant e, yields

    J/(r+2+J/a^2)<=delta<=J.                         (4)

The lower-bound algebra remains valid even if 1-R_u/a^2 is negative. Complex trial vectors give the same statement by separating real and imaginary parts, or directly using the real covariance matrix's maximal eigenvalue. No simplicity of the lowest eigenvalue is needed.

Let z0=2(r+1)/(r+2), so integral w phi^2=z0 a^2 and 0<=J/a^2<=z0. Set B=r+2+z0. Equations (3)--(4) prove the unconditional quantitative bound

    D>=A_global J^2,
    A_global=k1 a^(2gamma-4)/B^2.                    (5)

In particular J<=B a^(2-gamma) sqrt(D/k1) for every allowed orientation. This supplies the missing implication from a small deficit to a small weighted orientation distance within the fixed-profile class.

## 3. Upgrade to the global linear comparison

Use the already independently validated I264 local lemma: if J<=tau(a,gamma), then

    D>=c_local J, c_local=m_gamma/[4(r+2)],
    m_gamma=gamma a^(2gamma-2) min{1,(7/8)^(gamma-1)}.

The explicit positive tau is exactly the one in I264, which I265 checked without repairs. This note does not silently replace its constants. Alternatively the explicit changed local radius constructed in I266's direct comparison would suffice.

For J>tau, (5) gives D>=A_global tau J. Hence

    c_global=min{c_local,A_global tau}>0             (6)

proves the lower half of (G) for all J.

For the upper bound, if J<=a^2/8 then (4) gives 0<=delta<=a^2/8. Dropping all other nonnegative spectral moments and applying the mean-value theorem gives D<=M_gamma J, where M_gamma is the I264 upper coefficient. If J>a^2/8, simply use D<=a^(2gamma)<8a^(2gamma-2)J. Therefore

    C_global=max{M_gamma,8a^(2gamma-2)}               (7)

works globally. The case J=0 is exactly the constant-projector scalar equality case.

## Status and novelty limits

The new step is (1)--(3): the sharp exponent family is tangent to the fixed soliton cost at the target exponent, and optimizing a nearby lower exponent detects a loss in the lowest binding energy. Combined with the global elementary comparison (4), it removes any initial closeness assumption. The validated local estimate then upgrades the global square-root modulus to the global linear comparison.

This does not solve stability near arbitrary multi-channel optimizer profiles. The new implication and global fixed-profile scope require independent correctness and contribution reviews; a short proof does not itself certify substantiality or novelty. The prior I266 TECHNICAL verdict is preserved and has not been appealed by relabeling the same statement. No additional accepted finding is claimed.
