# Integrated full-radius calculation — paid source/classical composition

PREFREEZE / no nominee. These are research calculations and an explicit compatibility comparison, not a frozen new theorem, an independent correctness/contribution assessment, or a manuscript. The source and its operative proofs are stipulated. The positive-order application below closes by standard operations already in the actual primary bodies. Its importance or extension of a numerical exponent does not make the substitution substantial.

## 1. Exact objects and strongest input

Work on R^3 with Fourier transform fhat(xi)=integral exp(-ix.xi)f(x)dx and inverse factor(2pi)^-3. Define

 B_R^delta f = F^-1[(1-|xi|^2/R^2)_+^delta fhat], R>0.

For a scalar path a on an ordered interval I, V_r(a:I) is the supremum, over all finite increasing sequences t_0<...<t_N in I, of (sum_i |a(t_i)-a(t_(i-1))|^r)^(1/r). It is a seminorm; a base value is unnecessary when separately controlled. N_lambda uses disjoint ordered increments s_1<t_1<=s_2<t_2<=..., each of magnitude>lambda. Inverting t=1/R reverses order but preserves these quantities.

The examined full application is, for each fixed 2<=p<infinity, r>2 and delta>s(p):=max(0,1-3/p),

 ||V_r(B_R^delta f:R>0)||_p <= C_(p,r,delta)||f||_p.                 (A)

All radii and arbitrary Lp inputs are included; no radiality, fixed input frequency, finite radius range or finite number of samples is imposed. No bound uniform as delta decreases to s(p), or as r decreases to2, is asserted. The comparison also pays

 sup_(lambda>0) ||lambda N_lambda(B^delta f)^(1/2)||_p
       <= C_(p,delta)||f||_p.                                      (J)

The supremum is OUTSIDE the Lp norm. The stronger inside-supremum jump norm and full V2 are not asserted.

Source078 Section12 supplies fixed-radius scalar estimates, including uniform amplitude classes. But its own introduction points to a stronger input for the intended operation: the actual pinned critical-local-smoothing companion, physical-wave Section9. It gives, for every epsilon>0 and every fixed smooth annular symbol chi,

 ||exp(iu|D|) chi(D)f||_(Lp_x L2([R,2R],du/R))
       <= C_(p,epsilon,chi) R^(s(p)+epsilon)||f||_p, R>=1.          (W)

Indeed scale y=x/R, u=Rv, so chi(D_x) becomes a smooth symbol at frequency R in y, apply the companion annular estimate/full-range proof, and use L2([1,2])<=Lp([1,2]) for p>=2. The spatial dilation factors cancel. Negative times follow by complex conjugation/reflection. On bounded time intervals the fixed-annulus multipliers have uniformly integrable kernels. At p=2 the energy estimate even removes epsilon, but this improvement is unnecessary. We keep epsilon fixed until the end.

The local-smoothing proof was read through its actual input-slice localization, predecessor-volume/Jacobian calculation, synthesis, annular proof and interpolation, not inferred from the title. Earlier internal round/entropy/cylinder proofs are stipulated but were not read in their entirety.

## 2. Temporal Plancherel pays the thin radial square function

Let 0<h<=1/16. Initially take the ADDITIVE radial family

 F_(h,s)f = F^-1[psi((s-|xi|)/h) chi(xi) fhat], s in R,

where psi is smooth compactly supported in a fixed interval and chi is supported in a fixed annulus. Fourier transformation in s gives the exact formula

 F_s[F_(h,s)f](u) = h psihat(hu) exp(-iu|D|)chi(D)f.

Thus, pointwise in x, Plancherel identifies its L2_s norm with

 (h^2/(2pi) integral_R |psihat(hu)|^2
                         |exp(-iu|D|)chi(D)f(x)|^2 du)^(1/2).

There is no exchange of Lp_x and L2_u in the wrong direction. Apply triangle in Lp_x(L2_u) to a dyadic partition of u, and use(W). The |u|<=1 term is O(h)||f||p. The remaining bound is

 C h sum_(R=2^ell>=1) (1+hR)^(-N) R^(s(p)+epsilon+1/2)||f||p
       <= C h^(1/2-s(p)-epsilon)||f||p,                            (2.1)

provided N>s(p)+epsilon+1/2. The estimate follows by splitting the geometric sum at R comparable to h^-1. All constants use finitely many Schwartz seminorms of psi. Replacing psi by psi' gives the derivative estimate with an additional h^-1.

The multiplicative family needed for B_R is

 T_(h,s)f = F^-1[psi(h^-1(1-|xi|/s)) fhat], 1<=s<=2.

A fixed annular cutoff chi=1 on its frequency support can be inserted. Set u=(s-|xi|)/h. Then the profile is psi(u/s). Choose a smooth cutoff eta(s)=1 on[1,2], supported inside a fixed positive interval. The function b(s,u)=eta(s)psi(u/s) has fixed compact support in both variables and uniform smooth seminorms. Its Fourier transform in s gives

 b(s,u)=(2pi)^-1 integral exp(i lambda s) b_lambda(u)d lambda,

where every fixed Schwartz seminorm of b_lambda decays faster than any fixed inverse power of 1+|lambda|. Apply(2.1) to b_lambda, integrate in lambda by Minkowski, and obtain the same bound for T. Differentiating s adds either lambda or h^-1 times a uniformly smooth profile; both are paid by the decay. Reciprocal changes s=1/t on compact positive intervals preserve all these estimates and dt/t is equivalent to ds.

This is the actual temporal-Plancherel mechanism in LRS1012.2159v2 Proposition wavefrloc, and JSW Lemma8.1's proof, with the source improving the wave input. LRS gives it in the opposite direction for its application; the identities are reversible. Smooth-profile conversion is explicitly in JSW pp31–32. No new restriction or independent-profile L2 estimate is introduced.

Write A_h=C h^(1/2-s(p)-epsilon). Then on a fixed multiplicative time window, both T_(h,t) and h t partial_t T_(h,t) map Lp_x into Lp_x(L2_t) with norm at most A_h. This assertion is uniform in the smooth profiles used below.

## 3. The logarithmic all-scale operation is already classical

Uniform local operator bounds alone do not justify square summing arbitrary dilates. That tempting missing-interface claim is paid by the stronger primary theorem actually printed in JSW p33 (within the proof of Lemma8.2): if smooth multipliers m_s,1<=s<=2, are supported in a fixed annulus, their local Lp_x(L2_s) norm is at most A, and their xi derivatives through d+1 have bound B, then

 ||(sum_k integral_1^2 |F^-1[m_s(2^k xi)fhat]|^2 ds)^(1/2)||p
       <= C_p A [log(2+B/A)]^|1/p-1/2| ||f||p.                    (3.1)

The displayed general statement is for every1<p<infinity; its scope is wider than the p-range in the spherical-means heading of Lemma8.2. It is credited there to Seeger's1988 convolution theorem and its vector-valued version. We inspected the rendered page to verify the quantifiers, exponent, derivative count and norm order. This primary body quotes the general theorem rather than proving it. Access to the original1988 article failed; transitive proof reading is incomplete. That is a reading limitation, not a new mathematical gap.

For the thin bump, d=3 and xi derivatives through4 are bounded by C h^-4. The normalized derivative h t partial_t m has the same bound (with one extra fixed profile derivative). A finite smooth angular/radial partition puts any enlarged annulus into the stated fixed annulus. Hence (3.1), including dilation invariance of A, gives

 ||G_h f||p + h ||H_h f||p
     <= C (1+|log h|)^theta h^(1/2-s(p)-epsilon)||f||p,            (3.2)

 theta=|1/p-1/2|,
 G_h=(integral_0^infinity |T_(h,t)f|^2 dt/t)^(1/2),
 H_h=(integral_0^infinity |t partial_t T_(h,t)f|^2 dt/t)^(1/2).

The logarithm costs a polynomial in the bump index, NOT a fixed positive loss in the radius scale and NOT an uncontrolled constant for epsilon depending on scale. We use one fixed epsilon throughout.

## 4. Short variation AND dyadic samples

For a smooth scalar path a on[1,2], extension by a fixed cutoff to[1/2,4], the Besov-to-variation estimate of JSW equation(39) with rho=2 and the elementary interpolation bound give

 V2(a:[1,2]) <= C ||a||_(L2[1/2,4])^(1/2)
                       (||a||_2+||a'||_2)^(1/2).                 (4.1)

The corresponding point evaluation |a(1)| obeys the same bound. One can also obtain the latter directly from the fundamental theorem of calculus applied to |a|^2. The +||a||2 term accounts for cutoff derivatives and constants; it must not be silently omitted on a bounded interval.

Apply(4.1) after t=2^k s, then square, sum k and use Cauchy–Schwarz in k. The enlarged windows have bounded overlap in dt/t. With

 S2(T_h f)=(sum_k V2(T_(h,t)f:[2^k,2^(k+1)])^2)^(1/2),
 D2(T_h f)=(sum_k |T_(h,2^k)f|^2)^(1/2),

we get pointwise

 S2(T_h f)^2 + D2(T_h f)^2 <= C G_h f (G_h f+H_h f).

Holder in x and(3.2) therefore imply

 ||S2(T_h f)||p + ||D2(T_h f)||p
      <= C (1+|log h|)^theta h^(-s(p)-epsilon)||f||p.              (4.2)

This pays both the short variation and the dyadic samples. Leaving a separate arbitrary-dilate R-boundedness gap after(3.1), or inferring(3.1) just from scalar uniform boundedness, would both misstate the strongest reduction.

## 5. Sum the actual squared-radius multiplier

Choose a smooth radial b0 with compact support in the unit ball, equal to (1-|xi|^2)^delta for |xi| bounded away from1. The nonsmooth remainder can be written exactly as

 (1-|xi|^2)_+^delta = b0(xi) + sum_(j>=j0) 2^(-j delta) m_j(xi),  (5.1)

where m_j(xi)=psi_j(2^j(1-|xi|)), the psi_j have fixed compact support in a positive interval and uniform smooth seminorms. Indeed (1-r^2)^delta=(1-r)^delta(1+r)^delta, and on a boundary-distance partition u=2^j(1-r), the second factor is(2-2^-j u)^delta. The latter stays uniformly smooth on the fixed u support. Finitely many initial pieces are harmless. b0 is a smooth function of xi at0; do not choose a radial cutoff with a singular derivative there.

Let E_t be the sum of the boundary pieces in(5.1) at t xi. For each fixed p,delta with delta>s(p), set epsilon=(delta-s(p))/2>0 BEFORE summing. By triangle in the variation and l2 norms and(4.2),

 ||S2(Ef)||p + ||(sum_k |E_(2^k)f|^2)^(1/2)||p
  <= C sum_j (1+j)^theta 2^(-j(delta-s(p)-epsilon)) ||f||p
  < infinity.                                                    (5.2)

The constants depend on p,delta and the fixed profile choices. The sum is a convergent positive geometric sum with polynomial factor; no epsilon-removal and no uniform limit delta->s(p) is attempted.

Any finite ordered partition of(0,infinity) can be split into increments lying in one dyadic interval and increments crossing dyadic boundaries. Splitting each crossing increment at its first and last dyadic endpoints bounds V_r(E) by a constant times

 (sum_k V_r(E:[2^k,2^(k+1)])^r)^(1/r)
       + V_r(E_(2^k):k in Z).

For r>=2, the first is bounded by S2(E). For any sequence e_k,

 V_r(e_k) <=2(sum_k |e_k|^r)^(1/r) <=2(sum_k|e_k|^2)^(1/2).

Thus(5.2) actually pays full V2 for the BOUNDARY REMAINDER E. This is a cancellation remainder with square-summable dyadic samples; it is not the full family with its constant low-frequency tail.

## 6. Smooth low-frequency family and full conclusion

Let L_t=b0(tD). Its kernel is Schwartz and b0(0)=1. The classical smooth-approximate-identity variation estimate gives

 ||V_r(L_t f:t>0)||p <=C_(p,r,b0)||f||p, 1<p<infinity,r>2.         (6.1)

Here is the precise connection to the actual JSW proof. Choose a compactly supported smooth physical kernel phi with integral1. JSW Theorem1.1 gives dyadic jumps and r-variation for phi_t*f; its proof compares the smooth convolution to dyadic conditional expectations via a square function, with L2 almost orthogonality and the weak(1,1) cancellation calculation in Section4. The short variation follows from the smooth kernel square functions and(39), as in Section6. Replacing phi by the Schwartz inverse transform of b0 adds a mean-zero Schwartz kernel. Its dyadic samples and time derivatives satisfy the usual vector-valued Calderon–Zygmund square-function bounds: the low-frequency Fourier transform is O(|xi|), high-frequency transform decays rapidly, and kernel differences have integrable geometric bounds. Consequently this change adds a controlled full V2 remainder. This avoids incorrectly applying Theorem1.1's compact-support hypothesis directly to a noncompact kernel. It is the same smooth-kernel operation already used inside its proof.

Combining(5.2),(6.1) proves the comparison(A) for Schwartz inputs. The same decomposition, JSW's dyadic jump estimate, and Lemma1.3 pay(J). For E alone lambda sqrt(N_lambda(E))<=V2(E). This does NOT use a false pointwise conversion from a uniform-in-lambda Lp estimate to a strong variation norm. The full r>2 variation follows directly from(6.1) plus V2(E), so the p0<2<p1 condition in JSW Lemma2.1 does not have to be re-established for the nonsmooth Bochner–Riesz family.

Extend from Schwartz inputs to all Lp as follows. The known maximal bound controls a base value and the variation estimate controls all increments; choose a Schwartz approximating sequence with summable Lp successive differences. Almost everywhere, the successive family differences have summable supremum and variation seminorms. They converge uniformly in radius to a common continuous representative on(0,infinity), agreeing with the bounded operator at each fixed radius. Finite rational partitions are countable and dense by continuity; Fatou passes the estimates. No exceptional set depending on an uncountable choice of radii is introduced.

## 7. Research consequence

The full intended positive-order/all-radius/r>2 application is paid by the pinned local-smoothing input, temporal Plancherel, the existing logarithmic vector multiplier theorem, and classical short/long variation. This calculation is stronger than the first local-radius estimate, but still a source/classical composition. A large exponent improvement supplied by the stipulated source is not an author-created nonroutine operation.

There is no remaining claimed global-square-function or long-variation obstacle in this route. No critical-order endpoint, arbitrary radial-profile L2 estimate, unrestricted weak2-variation norm, or full V2 statement is nominated as a replacement. r85/r87 and all user-listed old targets remain unchanged. No full new author-proof nominee is submitted. The unresolved discovery obligation is to find and close an additional nonroutine operation; this round has not done so. That is not an impossibility or family-exhaustion assertion.

### Explicit smooth-kernel square-function check
For the smooth correction K=F^-1(b0-phihat), K is Schwartz and integral K=0. Let K_t(x)=t^-3 K(x/t). The Hilbert-valued kernel H(x)={K_t(x)}_(t>0) satisfies

 ||H(x)||_(L2(dt/t)) <=C|x|^-3,
 ||nabla H(x)||_(L2(dt/t)) <=C|x|^-4, x!=0,

by the substitution t=|x|/v and the Schwartz bounds; the near-v=0 powers are integrable. Its Fourier multiplier has uniformly bounded Hilbert norm because m(xi)=O(|xi|) near0 and decays rapidly at infinity. Plancherel and the standard Hilbert-valued Calderon–Zygmund theorem give the global square-function bound. The same applies to t partial_t K_t, whose multiplier is xi.nabla m and whose integral vanishes. Dyadic sampling uses either the same bounds with the l2 kernel or(4.1). Thus the full V2 correction used above is quantitatively paid; the smooth replacement does not require a new transitive estimate peculiar to this source.
