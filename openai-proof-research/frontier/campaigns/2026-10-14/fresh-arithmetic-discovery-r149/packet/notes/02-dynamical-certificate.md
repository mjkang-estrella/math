# Prefreeze: explicit finite dynamical certificate

This is a derivation for the actual Source050 matrices, not a frozen theorem or a nominee. Source proofs are stipulated. No eigenvalue experiment is used as proof.

## 1. Algebraic coordinates

Put a=exp(iπ/3), s=1/2−i(1+2√2)/(2√3), c=√2/3,
A=diag(a,a^−1), B=((s,1),(c,1−s)), and T=AB. Write

    t=1+√2, Δ=√(2√2−1), r=(t+Δ)/2>1,
    k=(1−√2)/(2√3).

Then T11=t/2+ik, T22=t/2−ik, T12=a, T21=a^−1 c.
The eigenvalues are r,r^−1. The nonzero row covectors

    ell_+=(T21, r−T11), ell_-=(T21, r^−1−T11)

satisfy ell_± T=r^(±1) ell_±. They are independent since T21≠0 and r≠r^−1. Let L be the matrix with these rows. Its squared Hilbert–Schmidt norm is

    C_L=2|T21|²+|r−T11|²+|r^−1−T11|²
       =4/9+2√2/3.

No unitary diagonalization of the generally nonnormal T is asserted.

## 2. A smooth Lyapunov function

On P1 define

    w([z])=|ell_+ z|²/(|ell_+ z|²+|ell_- z|²),
    g=w∘T−w.

Both are smooth real functions. With u=|ell_+ z|² and v=|ell_- z|²,

    g([z])=(r⁴−1)uv/[(r⁴u+v)(u+v)]≥0.

Its zero set is precisely the two T eigenlines. Moreover

    g([z]) ≥ (1−r^−4) |ell_+z ell_-z|²/(C_L² ||z||⁴).

This uses u+v≤C_L||z||² and r⁴u+v≤r⁴C_L||z||².

The product factors without additional radicals:

    (ell_+z)(ell_-z)=T21 q(z),
    q(z)=T21 z1²+(T22−T11)z1z2−T12 z2².

Indeed the constant coefficient in the product equals
(r−T11)(r^−1−T11)=−T12T21, by det T=1.

## 3. Order-three averaging gives a stated constant

Let omega=a², a primitive cube root of unity. Since A is unitary in the original coordinates,

    q(A^jz)=alpha omega^j z1²+beta z1z2+gamma omega^−j z2²,
    alpha=T21, beta=T22−T11, gamma=−T12.

Orthogonality of the three cube-root characters gives EXACTLY

    sum_(j=0)^2 |q(A^jz)|²
      =3[ (2/9)|z1|⁴+|beta|²|z1z2|²+|z2|⁴ ]
      ≥ (1/3)(|z1|²+|z2|²)².

For the final inequality, drop the nonnegative mixed term, bound both fourth-power coefficients below by2/9, and use x²+y²≥(x+y)²/2 for x,y≥0. Thus

    Phi:=g+g∘A+g∘A² ≥ c_dyn,
    c_dyn=2(1−r^−4)/(27 C_L²)>0.                 (1)

This bound is explicit in the actual algebraic matrix entries. It does not invoke a numerical minimum, unspecified compactness constant, or a spectral gap theorem.

## 4. Two explicit coboundaries

Set

    h_A=3w+2g+g∘A,   h_B=3w∘A.

The convention is T=AB, so Tz=A(Bz). Direct telescoping gives

    (h_A∘A−h_A)+(h_B∘B−h_B)=Phi.               (2)

Indeed the w terms sum to3(w∘AB−w)=3g; the remaining A terms sum to g∘A+g∘A²−2g. Notice that the coefficient in h_A is3, not the5 that would arise from also using B-translates.

For a finite positive Borel measure mu, (1)–(2) imply

    c_dyn mu(P1)
       ≤ int h_A d(A_*mu−mu)+int h_B d(B_*mu−mu).  (3)

The right side is signed, but the sum is positive. In particular, with total variation defined as the dual norm of sup-norm-bounded real continuous tests,

    c_dyn mu(P1) ≤6||A_*mu−mu||TV+3||B_*mu−mu||TV. (4)

Here 0≤w≤1 and0≤g≤1 give ||h_A||∞≤6, ||h_B||∞≤3. The same exact identity gives a bound in ANY weaker measure dual norm containing these two smooth tests, with their actual corresponding norms. One must state those norms; weak convergence alone gives no numerical rate.

For the source limiting line curvature, mass=48π and the two defects are exactly zero, recovering its contradiction by a finite smooth certificate. This is a quantitative payment of the DYNAMICAL part, not an effective threshold for E_m.

## 5. What (3) does and does not consume

To use this at finite m, one must actually construct a positive measure mu_m of controlled nonzero mass and bound its pairings with these TWO explicit coboundaries, or construct an equivalent smooth adjoint test on the original bundle. Generic distance-to-invariance assertions or almost-everywhere graph identities do not provide that operation.

This note is retained as a prefreeze calculation. The finite-order average and elementary Lyapunov telescoping are available classical operations; no substantial-contribution verdict is assigned to them, and they are not substituted for the complete requested bridge.
