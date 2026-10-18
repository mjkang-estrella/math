# A shifted-product calculation — pre-freeze technical candidate screen

No campaign theorem was frozen. This calculation arose after the unshifted-product obstruction was saved. It does not solve that earlier contemplated interface and is not a narrowed frozen target. All results below are author deductions under the stipulated source108 contracts; no independent review or contribution verdict.

Let s>=1, d_j>=2, r_j>=2 and let G_j be nonzero homogeneous complex forms of degree r_j in disjoint d_j-variable blocks, each defining a smooth projective hypersurface. Put D=sum d_j, R=sum r_j, and H=product G_j-1.

## Exact certificate

There is a linear functional ell=sum ell_j for which H=0 and the D-1 constant directional derivatives of H along a basis of ker ell have exactly

    mu = R product_j (r_j-1)^(d_j-1)

simple zeros in affine D-space.

Indeed the projective gradient map gamma_j:[x]->[dG_j(x)] is everywhere defined. Euler's identity and smoothness exclude any simultaneous zero of its coordinate derivatives. The pullback of O(1) is O(r_j-1); this ample line bundle makes the map finite, and its degree is (r_j-1)^(d_j-1). In characteristic zero its generic fibers are reduced. Choose ell_j off the branch locus and off the image of V(G_j). Each of its gradient preimages has G_j nonzero and ell_j nonzero by Euler's identity. Normalize its representative v_j by ell_j(v_j)=r_j. Then dG_j(v_j)/G_j(v_j)=ell_j.

At H=0, the gradient of H is the block tuple dG_j/G_j. Thus a critical point of ell on H=0 has dG_j(x_j)/G_j(x_j)=lambda ell_j simultaneously. Lambda is nonzero (Euler). It has uniquely the form x_j=v_j/lambda for a tuple of the selected projective points. Its remaining equation is

    lambda^R = product_j G_j(v_j).

It has R distinct nonzero roots. This proves the exact cardinality and excludes all other solutions.

To check simplicity, let delta x be killed by the full square Jacobian of H and its D-1 polars at such a point. Then delta H=0 and delta(grad H) is proportional to ell. Since grad H=grad(product G_j) and product G_j=1, its variation on a tangent vector with delta H=0 is the variation of the block logarithmic gradients. Passing to projective block covectors, the latter has zero variation. Etaleness of gamma_j forces delta x_j=t_j x_j. Homogeneity gives delta(dG_j/G_j)=-t_j lambda ell_j. The common proportionality forces all t_j=t. Finally delta H=sum r_j t_j=R t=0, hence t=0. The square Jacobian is injective, therefore invertible.

## Direct application of the paid source certificate

Source108 Proposition polar:ambient-bound, with h=D-1 and the identity affine slice, gives

    bdc(H) >= D/(4e) [R product_j (r_j-1)^(d_j-1)]^(1/D).

This uses its full arbitrary coefficientwise-border statement unchanged. No determinant representation is modified by constant subtraction.

For equal blocks r,d, the right side is

    sd/(4e) (sr)^(1/(sd)) (r-1)^(1-1/d).

Taking the source smooth affine permanent projection for k=floor(m/11)>=128 gives r-1>=k/4 and d-1>=k²/200. Here r-1<=k and d>=k for k>=128, so (r-1)^(1/d)<=2. Therefore

    bdc(product_{j=1}^s per_m(X_j)-1) >= s k³/(6400e)

for all s>=1 and m>=1408. The last constant is deliberately loose: d>=k²/200 and (r-1)^(1-1/d)>=k/8 give s k³/(6400e). Affine monotonicity supplies the implication. This is a complete deduction, but the remaining work is predominantly attribution and deciding whether the operation meets the campaign substantiality standard.

## Operative comparison and current assessment

The determinant-side kernel incidence, persistence of simple points and coefficient extraction are entirely source-paid. Sheshadri, arXiv2606.13628v1, Theorem3 and its complete ordinary proof in Section3.1 supply the primary ancestor: count transverse conormal points; unique corank-one kernel lift; Schur-complement elimination; multihomogeneous Bezout. Those operations are not claimed here. The new calculation merely supplies a different explicit finite certificate to the already general source Proposition polar:ambient-bound.

Dolgachev, Polar Cremona transformations, retrieved PDF arXiv:math/0005048v2, Section2 (pp2–4), explicitly uses the logarithmic gradient and its homogeneous radial scaling, crediting Etingof–Kazhdan–Polishchuk. The separate-block factorization of logarithmic gradients is immediate from d log(product G_j)=direct sum d log G_j. The calculation above does not introduce a new deformation, incidence, or complexity lower-bound mechanism beyond those existing operations. Consequently the author assessment is TECHNICAL, not a substantial nomination, despite the all-s bound. Absence of an exact shifted-permanent statement in bounded search is not evidence of novelty.

## Actual reading limits

For Sheshadri, retained PDF SHA256 e8664e34766ddee525c9ac039ecd591dd6525d97df043712aee943b1aa0c25a8 from https://arxiv.org/pdf/2606.13628v1. Read local text lines150–420 and480–730, including Theorem3, multiplicity-one definitions, full Section3.1 proof; additional actual HTML contexts of abstract, Sections1.5,4,5 and final limitations were returned/read. Did not read the entire specialization proof, symmetric proof or appendices.

For Dolgachev, retained PDF SHA256 028226872dbcd8572b533fbf48eac0fbe0ea706ae8a010141cfe333103e5821d from https://arxiv.org/pdf/math/0005048 (PDF identifies v2,16May2001). Read local text lines1–210, complete pp1–4 including Section2 and start of Section3. The rest is unread. The separate HTML v1 was opened only; no conflation of versions.

Neither PDF was visually inspected in this screen. No numerical computation was needed for the exact argument. This note is screening evidence and not an independent proof gate.
