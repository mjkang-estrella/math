# Enlarging the slice space: checked conditional construction

Author continuation of T101G69. This is not a review or a proof of the frozen global theorem. Throughout this note B=I and d=||D||op is sufficiently small by an absolute amount. Neither assumption has been obtained at trace-paid cost from the full target. Parent supplied the cb near-projection/lower-H route and coefficient-tensor product estimate; the identities and bounds below combine that collaboration with the preceding channel note. All norms and traces are unnormalized.

## 1. A completely bounded spectral projection

The E/F row and column identities in channel-density.md also prove

  ||K²−K||cb <= e := 2sqrt(2d)+2d.

Indeed elementary-operator Cauchy–Schwarz applies at each matrix amplification with the same row and column Grams. This is not an inference from the induced Hilbert–Schmidt norm. Suppose e<1/8. In the Banach algebra of completely bounded maps set

  Z0=(I+4(K²−K))^(-1/2),
  Pi=(I+(2K−I)Z0)/2.

The inverse square root is the absolutely convergent binomial series. Commutation of its factors and (2K−I)²=I+4(K²−K) show Pi²=Pi. The real spectral formula identifies Pi with 1_[1/2,1](K). Since ||K||cb=1,

  ||Pi−K||cb <= 12e.                                    (1)

For example ||Z0−I||cb <= (1−4e)^(-1/2)−1 <=8e and ||2K−I||cb<=3. Pi(I)=I. Write t=2e; every eigenvalue of K on W=range Pi is in [1−t,1]. Its complement has eigenvalues <=1/2. The previous note gives

  dim W=m+r,   0<=r<=8C,
  ||Pi−S||HS<=2sqrt(2C).                                (2)

Injectivity of Pi J gives the nonnegative r, using d<1/2.

The space W consists of real symmetric matrices. To see this without an assumption on positivity of Pi, for skew Z differentiate the orthogonal action on T. Direct expansion gives

  ||(Z acting on all three modes)T||²
       =3||Z||F²−6<Z,KZ> >=0.

Thus K has spectrum <=1/2 on skew matrices. Since e<1/8 excludes the eigenvalue 1/2, W has no skew component.

## 2. Upper and lower row Gram

Choose an HS orthonormal real symmetric basis Y_a of W and put H=sum_a Y_a². Partial trace is taken on the positive operator on the full matrix Hilbert space, not on the CP ordering of maps. Direct vectorization gives

  Tr_2(K²)=sum_rs tr(Xr Xs) Xr Xs=I.

The spectral inequality Pi <=(1−t)^(-2) K² therefore gives

  H <= h0 I,  h0=(1−t)^(-2).                            (3)

Kadison and the tetrahedral cross identity give

  sum_r(KXr−Xr)² <=2D.

The cb estimate (1), applied to the row matrix of Xr, consequently gives row-operator norm

  ||row(Pi Xr−Xr)|| <= h1:=sqrt(2d)+12e.

The row operator of Xr has Gram I. Hence sum_r(Pi Xr)² >=(1−h1)²I when h1<1. Since Pi S Pi<=Pi, partial trace gives

  (1−h1)²I <=H<=h0 I.                                  (4)

In particular kappa:=||H−I||op tends to zero with d, independently of m. We also have the trace-paid estimate

  ||H−I||F <=(sqrt(h0)+1)||Pi−S||HS.                    (5)

For completeness, use all matrix units as an orthonormal basis and express H and I as the row Grams of the matrix families Pi(Eij) and S(Eij). Their difference in family HS norm is ||Pi−S||HS. Factoring the difference of the two row Grams proves (5); no factor m occurs.

## 3. Trace-paid and operator-small leakage

Let M(ea tensor eb)=YaYb and Z=(I−Pi)M. Put z=||Z||op, zH=||Z||HS, and let

  L_ab=sum_c <Z_ac,Z_bc>,   ell=||L||op.

Transposition sends Z_ab to Z_ba, so both one-input Grams have the same norm ell.

The parent trace calculation gives

  sum_ar ||[Xr,Ya]||F² =2tr Pi(I−K)<=12C.               (6)

One verification is to write s_lambda=<v_lambda,Sv_lambda>. Then C=sum(1−lambda)s_lambda, the low s-mass is <=2C, and high (1−s)-mass equals r plus the low s-mass. Thus tr Pi(I−K)<=2C+r/2<=6C.

The spectral gap on W-perp is g>=1/2 in I−K. Dirichlet energy is E(V)=sum_r||[Xr,V]||F²=2<V,(I−K)V>. In particular

  ||(I−Pi)V||F² <= E(V)/(2g).

Leibniz, row/column Cauchy–Schwarz, and (3),(6) give

  zH² <= (2h0/g) sum_ar||[Xr,Ya]||F² <=48h0 C.         (7)

For a general coefficient matrix (v_ab), group the first Leibniz term by rows and the second by columns. Each resulting linear combination lies in W and has Dirichlet energy at most 2t times its squared HS norm. Consequently

  z² <=4h0 t/g <=8h0 t.                                (8)

This is a bound on the full coefficient-tensor operator, not just on individual products.

To control the other flattening, define

  G=sum_ra [Xr,Ya]^*[Xr,Ya]
    =K(H)−H+2sum_a(1−lambda_a)Ya².

Choose the basis diagonalizing K. Because K is unital and positive,

  ||G||op<=2kappa+2t h0.

For a fixed Y in W, the two Leibniz terms and the same gap give

  sum_b||(I−Pi)(Y Yb)||F²
   <= (2h0 t+||G||op)||Y||F²/g.

Therefore

  ell <= (2kappa+4h0 t)/g.                             (9)

Both z² and ell tend to zero with d. Equations (7)–(9) retain their separate meanings: (7) is trace-paid; (8) and (9) are dimension-free operator estimates.

## 4. A fully symmetric cubic on the enlarged space

Define sigma_abc=tr(YaYbYc). Cyclicity and reversal make this fully symmetric. Its multiplication is Pi(YaYb), which is commutative since Pi kills skew matrices. Its Gram satisfies the exact identity

  B_sigma=G_H−L,
  (G_H)_ab=tr(YaYb H).                                 (10)

The displayed expression is symmetric because H,Ya,Yb are symmetric. It follows that

  ||B_sigma−I||op<=kappa+ell,
  ||B_sigma−I||F<=sqrt(h0)||H−I||F+sqrt(ell) zH.         (11)

For the HS inequality use sum_a||(H−I)Ya||F²=tr((H−I)²H) and ||L||F²<=ell tr L=ell zH².

There is an important reversal in the associator formula. The ambient matrices do not commute, so their two naive Frobenius product pairings need not agree. Instead,

  <YaYb,YdYc>=<YbYc,YaYd>

by cyclic trace. Projection is unchanged by reversing a product. Subtracting the projected pairings therefore expresses A_sigma as the difference of two permuted contractions <Z_ab,Z_dc> and <Z_bc,Z_ad>, with an overall sign depending on the associator convention. This proves

  ||A_sigma||HS<=2 z zH.                               (12)

Let eta(F) be the maximum operator norm over every one-versus-three and two-versus-two flattening of a four-tensor F, allowing every permutation of indices. Then

  eta(A_sigma)<=2 max(z²,ell).                         (13)

Here are the separate checks. The natural two-versus-two flattening of Z*Z has norm z². The crossed flattenings are elementary operators with Kraus matrices R_i=(<E_i,Z_ab>)_ab. Their row and column Grams have norm ell, so their induced HS norm is <=ell. For a fixed first input, the remaining matrix is the product of the corresponding Z slice and Z; its HS norm is <=z sqrt(ell). This bounds every one-versus-three flattening. Transposition exchanges the two input Grams, so no unproved one-sided estimate is used.

Thus sigma has operator-small Gram and ALL associator flattenings, while

  ||B_sigma−I||F²+||A_sigma||HS² <= absolute_constant*C. (14)

This resolves the latent nearly-fixed-mode compatibility at the level of an approximate symmetric product. It does not by itself construct an exact orthodeco tensor. An operator-density version of normalization/correction still needs to be fully written and checked before using (14) as a rounding result.

## 5. Full-target obligations remain

Even if the last correction is completed, this note assumes exact B=I and small ||D||op. It does not supply either of the two initial reductions from T101G69:

1. B<=2I with strong Frobenius Gram error must be converted to exact B=I at cost O(beta²+C).
2. Arbitrary D must be converted to small operator D with trace-paid losses, controlling subsequent leakage and without iterating an uncontrolled projection.

The r67 small-total-error normalizer does not establish either reduction. No independent proof verdict, campaign nomination, or all-error conclusion is claimed here.
