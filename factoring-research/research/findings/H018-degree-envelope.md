# H018 — Fixed-degree comparison and a linear-element candidate

2026-10-08. Parent analytic derivation, **accepted after independent review**
with the two local corrections below. The originally reviewed bytes are in
[the submitted draft](H018-submitted-draft.md), SHA-256
072060c6b244e526199b416de797b2336a3c220b9ab548adec382a770fb0cfe8.
No numerical experiment, implementation, parameter sweep or new Lean theorem.
Verified factoring complexity improvement: **NONE**.

The changed coefficient-line idea is not intrinsically a quadratic-element
method. Extending its current upper-population relaxation to r coefficients
gives an exactly optimizable model. In that relaxation, r=2 is best at every
fixed threshold parameter eta in [0,1]. An explicit linear-element witness has
optimistic envelope 1.90, but no useful population lower bound. A natural
stronger count suggested by homogeneity would eliminate the entire model's
apparent improvement. That stronger count is an obligation, not a proved fact.

This work is separate from H014's implementation review, H016's processing
construction, and H017's quadratic-tail supply task. H014 passed its review
while this derivation was being recorded; H016 and H017 remain active. Neither
their absent results nor this degree extension are assumed established here.

## 1. Fixed-r extension of the exact primitive

Fix an integer r>=2 independently of n=bit_length(N), and write k=r-1. Let
f be monic of degree d>k, with nonnegative integer coefficients and maximum
coefficient A>=1. Its intended construction is the ordinary base-m expansion
of N, with monicity checked. Let g have leading coefficient a in [1,H] and
its k remaining integer coefficients in [-H,H]. Reducible/imprimitive g and
zero resultants are included before any filtering.

Set V(X)=(X-1)^k, and write uniquely

    g(X) = a V(X) + h(X),       degree(h)<k.

For fixed r, h's coefficient labels each range over O_r(H) integers. There
are O_r(H^k) labels; intersecting all the original coefficient constraints
gives one exact rational interval for a, then its integer endpoints. Empty
lines are charged. The a=1 slice alone supplies (2H+1)^k distinct nonempty
labels. Thus this full-line algorithm really pays Theta_r(H^k) labels.

The line polynomial P_h(a)=Res(f,aV+h) has exact degree d, with leading
coefficient

    Res(f,V) = (-1)^(dk) f(1)^k != 0.

As in H014, it can be computed using exact resultant evaluations and
interpolation at polynomial bit cost when d, log A and log H are poly(n).
Exact real-root isolation of P_h-T and P_h+T, followed by direct integer tests
at the boundary intervals and in sign-constant gaps, gives the proposed
extension

    O_r((H^(r-1)+S_all)*poly(n)).                         (1)

H014's exact interval implementation and mathematical bit accounting have now
passed independent review. Equation (1) extends that construction; it is not
a new validated implementation. No degree-growing r claim is made: binomial
coefficients and the number of label dimensions cannot then be hidden in O_r.

A convenient integral norm bound is

    C0 = (rH)^d (d+1)^ceil(k/2) A^k.

Indeed |g(alpha)|<=rH*max(1,|alpha|)^k and the monic Mahler measure of f is
at most sqrt(d+1) A. The harmless rounding of k/2 only enlarges the bound.
For fixed rational eta in [0,1], put Q=k(1-eta) and

    T = floor(C0 N^(-Q/d)).                              (2)

If Q=v/w is nonnegative rational, its exact implementation is the largest
integer T>=0 satisfying T^(wd)*N^v<=C0^(wd). Integer powers and roots have
polynomial widths under the stated input promises. Acceptance remains the
closed condition |Res(f,g)|<=T, including T=0.

The elementary root-product count on each line, with leading coefficient
f(1)^k>=A^k, gives

    S_all <= poly_r(d) [H^r N^(-Q/d^2)+H^(r-1)].           (3)

This is an upper count only. It has the same crucial limitation as H013/H014:
it does not say how many primitive, irreducible, smooth or independent rows
exist. Filtering cannot reduce the output term of the enumerator retroactively.

## 2. The exact optimistic model

Use the existing notation D=(log N)^(1/3)(log log N)^(2/3), with

    log H=(a+o(1))D,  log B=(b+o(1))D,
    d=(delta+o(1))(log N/log log N)^(1/3),  a,b,delta>0.

All coefficients of g scale together with H; its degree k is fixed. The
rational value has the bound log|g(m)|<=k log N/d+log H+lower terms. With
(2), the combined norm-size coefficient in Card C's assumed smoothness law is

    K/delta+a delta,       K=k(1+eta).

Let u>0 denote the exponent of actual candidates attempted under that law.
Even granting usefulness of every success, its collection condition is

    u >= b + (K/delta+a delta)/(3b).                      (4)

The upper count (3), mandatory lines and conventional completion model give
the following relaxation:

    u <= s := max(ra-Q/delta^2, (r-1)a),
    c >= max(u, (r-1)a, 2b).                             (5)

These inequalities are not an established factorer. In particular, (4)
assumes a joint smoothness law for the selected tail, (5) grants enough actual
attempts below an upper bound, polynomial processing is still an obligation,
and completion/splitting is only the existing optimistic model.

**Proposed model theorem.** The infimum of c subject to (4)-(5) is

    c_*(r,eta)^3
      = 64(r-1)[(r+1)+(r-1)eta]/(9r^2).                 (6)

This statement is solely optimization of displayed real inequalities.

To prove the lower bound, u<=s implies at least one of two cases. If
u<=(r-1)a, then a>=u/(r-1). Apply AM-GM first in delta and then in b to
(4). With K/(r-1)=1+eta this gives

    u^3 >= 64(1+eta)/9.                                 (7)

If u<=ra-Q/delta^2, then a>=u/r+Q/(r delta^2). Hence

    K/delta+a delta >= (K+Q/r)/delta+u delta/r
                    >= 2 sqrt((K+Q/r)u/r),
    u >= 2 sqrt(2 sqrt((K+Q/r)u/r)/3),
    u^3 >= 64(K+Q/r)/(9r).                              (8)

The last expression is (6). It is strictly smaller than the right side of
(7): their difference is 64[1+(2r-1)eta]/(9r^2)>0. Since c>=u, either
case proves the lower bound.

For attainability in this relaxation, let u=c_*(r,eta), set

    L = rK+Q,
    b = u/2,
    delta = sqrt(L/u),
    a = u(L+Q)/(rL).

Then ra-Q/delta^2=u. Also (r-1)a<=u, since this is equivalent to
(r-2)Q<=rK, which holds for r>=2 and eta in [0,1]. Equality holds in
(4) by (8)'s two AM-GM equalities; all of (5) hold with c=u. Replacing u
by a slightly larger value in these same formulas gives strict collection
slack: the second term of (4) becomes proportional to u^(-1/2), whereas
u-b=u/2 increases. Thus strict excess does not change the infimum.

This proof never infers an actual candidate lower count. Attainment of the
relaxed inequalities is not attainment by a relation sampler.

## 3. Degree comparison and a concrete linear witness

After removing the positive factor 64/9, (6) equals

    F(r) = (1+eta)-2eta/r+(eta-1)/r^2.

As a real function on r>=2, its derivative is

    F'(r)=2eta/r^2+2(1-eta)/r^3 > 0.

Thus **more coefficients strictly worsen this particular optimistic model**
for every fixed eta in [0,1]. Actual useful supply can differ by degree, so
this is not permission to discard H017's independent quadratic supply question.
At eta=1, (6) recovers Card C's unfiltered 128(r-1)/(9r).

For r>=6, even eta=0 cannot beat the quoted Coppersmith constant c_C:

    c_*(6,0)^3 = 560/81 > (92+26 sqrt(13))/27 = c_C^3.

The strict inequality is exact: it reduces to 142>39 sqrt(13), whose squares
are 20164>19773. Monotonicity in both r and eta proves the rest. This closes
r>=6 only within (4)-(5), not alternative norm laws, completion algorithms,
field constructions or factoring generally.

For the simplest surviving case r=2, take the rational parameters

    eta=4/5,  a=1,  b=19/20,  delta=7/5,
    K=9/5,    Q=1/5.

They give

    s = max(2-5/49,1) = 93/49,
    b+(K/delta+a delta)/(3b) = 15101/7980,
    s - [b+(K/delta+a delta)/(3b)] = 313/55860 > 0,
    max(s,2b) = 19/10 = 1.90.                           (9)

The comparison 1.90<c_C is strict: after cubing it is equivalent to
sqrt(13)>93193/26000, and 13*26000^2=8788000000 exceeds
93193^2=8684935249. The primary
[Lee–Venkatesan Remark 4.31](https://arxiv.org/html/1805.08873v1)
states the comparison constant in a square-congruence setting; this report
does not upgrade that result or (9) to unconditional complete factoring.

The exact linear candidate is especially simple. Write g=aX+b_coeff,
1<=a<=H, |b_coeff|<=H, and beta=a+b_coeff. Enumerate
1-H<=beta<=2H, with

    max(1,beta-H) <= a <= min(H,beta+H).

There are 3H labels, including empty ones if a wider convenient range is used.
The polynomial to classify is

    P_beta(a) = Res(f,a(X-1)+beta)
              = sum_(i=0)^d f_i (-1)^(d+i) (beta-a)^i a^(d-i).

Its leading coefficient is (-1)^d f(1). Binomial expansion constructs it in
O(d^2) coefficient arithmetic, with polynomial bit widths, without a general
Sylvester determinant. The exact cutoff at (9) is

    |P_beta(a)|^(5d) N <= C0^(5d),
    C0=(2H)^d(d+1)A.

Apply the same certified sublevel routine and emit the accepted integers;
then filter gcd(a,b_coeff)=1. Positive leading coefficient fixes sign
normalization. Linear g needs no irreducibility test beyond this primitive
normalization. Zero norms require explicit handling, not a smoothness pass.
This describes an N-only candidate once the public degree/height are chosen;
it does not assume knowledge of a factor or of a useful embedding.

## 4. Homogeneity exposes the most important missing count

Equation (3) arises from a one-dimensional dth-root union bound. It may be
much too loose to support (9). The resultant is homogeneous of degree d in
the coefficient vector z of g:

    Res(f,lambda*g) = lambda^d Res(f,g).

Since C0(H) is exactly proportional to H^d, put epsilon=N^(-Q/d^2) and
R=H*epsilon. Before clipping the coefficient cube, the real sublevel set
at the unfloored threshold corresponding to (2) is exactly the dilation by R of

    B_f = {z : |Res(f,g_z)| <= r^d (d+1)^ceil(k/2) A^k}.

Floored integer acceptance is equivalent to the unfloored real threshold
at integer vectors. If a uniform lattice-point estimate of the following
strength could be proved, it would be a decisive stronger obstruction:

    S_all <= L_N[1/3,o(1)] * (R^r + H^(r-1)).             (10)

**Equation (10) is not proved here.** Even finite volume of B_f would not
by itself prove the necessary lattice discrepancy bound. Real-root cusps,
complex embeddings, near-coincident linear forms, coefficient dependence,
and growing d can make constants enormous or cause exceptional lattice
populations. Primitive restrictions do not automatically cure all of them.
The ordinary base polynomial's root geometry must be checked, not modeled
as uniformly well conditioned. Point counts cannot simply be replaced by
continuous volume.

Here is why (10), if valid in the required scope, is decisive inside the
unchanged smoothness model. It replaces s in (5) by

    s_sharp = max(ra-rQ/delta^2, (r-1)a).

The second branch of the same AM-GM proof then has a>=u/r+Q/delta^2,
so K+Q=2(r-1) gives

    u^3 >= 128(r-1)/(9r) >= 64/9.

The first branch still has (7), also at least 64/9. Thus no r>=2 and
eta in [0,1] would improve ordinary GNFS in this relaxation. This expresses
the cancellation between radial norm reduction and candidate volume loss;
it does not assert the needed uniform geometry or any computational lower
bound. A stratum of smaller coefficient height also has a smaller rational
norm, so a genuinely stratified replacement must recompute its full model
rather than apply (4) blindly to every stratum.

## 5. Disposition and next decisive action

The exact optimization and linear witness are **accepted analytic results**
after [independent review](H018-independent-review.md), not an experimental pass.
The comparison numerator and unfloored real-set wording were corrected as
requested; neither changes the model result. Equation (10) is a
precise proposed stronger count, not an accepted theorem. No result from this
report is added to the factoring baselines or installed as a solver.

H014's accepted review can now support the exact sublevel primitive; consume
H016/H017 when complete because their conclusions may settle further parts.
Review the generalization, AM-GM optimum, rational witness and its supply
distinction in a fresh owned task without duplicating those active questions.
If the linear construction survives, the highest-value next question is its
primitive tail population with growing degree, including cusp constants and
smaller-height strata. Another tiny admission-ratio fit would not settle it.

Small-value real-root regions are established NFS background, not a novelty
claim: [Murphy's thesis](https://maths-people.anu.edu.au/~brent/pd/Murphy-thesis.pdf)
discusses size/root properties in polynomial selection. The proposed delta
here is the exact output-sensitive enumeration and its conditional accounting;
no priority claim is made for that general computational primitive either.
Batch smoothness, ideal data, useful rank, square roots and proper splitting
remain separately paid. Verified factoring complexity improvement: **NONE**.
