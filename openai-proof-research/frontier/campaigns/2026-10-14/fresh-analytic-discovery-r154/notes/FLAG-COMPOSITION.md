# Feasibility calculation: the strongest paid flag composition

PREFREEZE / no nominee. This is a reconstruction of a source/primary reduction, not a frozen author theorem, independent grade, or priority claim. It records why the apparent gain does not supply a substantial operation. All dimensions below are Hausdorff dimensions. K3 is the pinned Source074 maximal paper; BD is Bright–Dhar2412.18193v2; H is Héra1809.04666v4.

## Parameters and the actual source interface

The concrete exploratory input is a Borel set F in R4,1<s<=2, and a nonempty set P of two-dimensional linear subspaces with dim P>=t,0<t<=4. For every V in P, there exists an affine translate V+a_V with dim(F intersect(V+a_V))>=s. No joint regularity of a_V, no Ahlfors regularity, and no positive area of these intersections is presumed. The calculation returns s+t/2. It is precisely the n0=3,k0=1 case of BD's explicitly stated conditional theorem following its main proof.

K3's hypotheses concern arbitrary L3 functions and arbitrary tube translations. Its S2 measure and cylinder normalization differ from G(3,1) and round-ended tubes only by fixed factors. The quotient R4/U for any line direction U is a Euclidean R3; an orthogonal identification changes no source constants. Thus the same C_epsilon works on every quotient, rather than a direction-dependent family of estimates.

## Do not assume a common good slice direction

Choose1<sigma<s (or sigma<2 when s=2). For each V, choose a compact subset of F intersect(V+a_V) with dimension>sigma and an appropriate finite positive-dimensional measure. Classical slicing gives a positive measure collection D_V of affine lines inside V+a_V meeting F in dimension at least sigma-1. It does NOT say every line direction inside V is good, nor that one fixed U works simultaneously for all V. The calculation averages over the full invariant flag U subset V.

Localize F to a bounded ball, reducing sigma and t slightly if necessary using countable stability. Normalize the ball by one fixed dilation. The translates a_V may be chosen normal to V and then are bounded whenever the intersection is nonempty. Restrict the plane-direction family to one on which the natural two-dimensional measure of D_V is at least m0>0, retaining dimension>t0 for any chosen t0<t after an arbitrarily small loss. This is countable localization of positive masses, not an invented uniform lower mass condition.

Let S be the set of all affine lines in R4 whose intersection with F has dimension at least sigma-1. We seek dim S>=2+t. The ambient affine line space A(4,1) has dimension6, while G(4,2) has dimension4. Those are the two different volume exponents that must be retained.

## A cover calculation with the epsilon sign and Jensen power retained

Cover S by balls B_j in its standard affine-line metric, with radii r_j<2^-K. Group them into J_m with delta=2^-m<=r_j<2delta. Let f_m be the indicator of the union of a fixed enlargement of these balls. On bounded parameter charts,

  integral_A(4,1) f_m <= C #J_m delta^6.                         (1)

For every V in the localized family, some m has at least c m0/m² measure of D_V covered at this scale, because sum_m c/m²<1. Call the corresponding set of plane directions P_m. These sets cover P'. They need not be measured directly: finite covers of them will suffice.

For U in G(4,1), write f_{m,U}(x)=f_m(U+x),x in Uperp. Define

  A_m(V)=integral_{U in G(V,1)} M_delta^U f_{m,U}(V/U) dU.

The operator is the line maximal operator on the three-dimensional quotient Uperp. BD's elementary rotation and translation comparisons, with fixed enlargement of the B_j, give

  A_m(W) >= c m0/m² whenever dist(W,P_m)<c delta.               (2)

The enlargement matters: a line lying on a cover-ball boundary need not remain inside the unexpanded ball after rotation. Rotating V to W moves both its line directions and bounded affine offsets by O(delta); the enlarged cover supplies an O(delta) margin. In quotient coordinates this margin fills a transverse delta-disc. Integrating the positive one-dimensional shift sets and dividing by tube cross-section delta² gives (2).

The probability Haar measure on the flag U subset V can be integrated in either order, since both constructions give the unique rotation-invariant probability measure on the same flag manifold. Jensen and K3 therefore give

  integral_G(4,2) A_m(V)^3 dV
    <= integral_flags [M_delta^U f_{m,U}(V/U)]³
    <= C_epsilon³ delta^(-3epsilon) integral_A(4,1) f_m.       (3)

The CUBE of the average stays in this inequality. In particular one cannot replace (integral M)^3 by integral M on a lower bound for a small mass.

Choose a maximal c delta-separated subset of P_m of size N_m. The disjoint smaller caps have total measure comparable to N_m delta^4 and lie in the neighborhood in(2). Combining(1)–(3),

  #J_m delta^6 >= c_epsilon m0³ m^-6 N_m delta^(4+3epsilon). (4)

The loss is delta^(+3epsilon) after rearranging, never delta^(-3epsilon). This sign still suffices for Hausdorff dimension because all target exponents are tested with slack.

Fix u<2+t0. Choose epsilon>0 such that u<2+t0-3epsilon. Then(4) implies

  #J_m delta^u
   >= c_epsilon m0³ m^-6 delta^(u-2-t0+3epsilon)
                 [N_m delta^t0].                           (5)

The exponent preceding the square bracket is negative. At sufficiently small scales its exponential growth dominates m^6. Summing(5) pays a fixed multiple of sum_m N_m delta^t0. The c delta-caps from all these finite nets cover P', so the last sum is bounded below by its positive t0-dimensional Hausdorff content. For each fixed sigma<s, this proves the desired dimension lower bound for S after t0 tends to t. Only the final bound for F is then passed to sigma approaching s; no limiting family S at the exact fibre exponent is asserted. No Frostman measure on each possibly nonmeasurable P_m is required, and no measurable selection V->a_V is inserted.

## Returning from line parameters to points

Héra's actual Theorem thm1 gives, for a>0 and a line family of dimension b in any Rn,

  dim F >= a+b/2,

when every line meets F in dimension at least a. Its proof first selects a common dyadic cover scale, then two separated positive-content parts on every selected line. A pair of separated small cubes determines the line to angular/intercept accuracy O(delta/separation). Counting incidence pairs yields the displayed inequality. The polynomial loss in the chosen scale is harmless for every strict Hausdorff exponent. The actual complete main counting proof and its geometric separation, metric-net and perturbation proofs were read, not just the theorem title.

Insert a=sigma-1 and b arbitrarily below2+t. The calculation gives

  dim F >= (sigma-1)+(2+t)/2 = sigma+t/2,

and then s+t/2. For t=4 this is s+2. It does not say F has positive4-dimensional measure at s=2.

The set-theoretic reductions are also classical. Héra cites the Elekes–Vidnyánszky analytic-fibre lemma proved in Héra–Keleti–Máthé1701.02299v3. Its actual proof was read: compact subsets in the fibre bundle, the Hausdorff hyperspace, Hausdorff-content capacity and Choquet capacitability make the content-superlevel plane family analytic; Gdelta hulls and countable restrictions justify dimension reductions. Choquet/Howroyd and the underlying slicing/Frostman originals are credited inputs, not claimed fully reread.

## The same quotient calculation already handles higher-dimensional codimension two

BD's proof, rather than just the displayed one-step conditional statement, uses a maximal input only on R^(n-k+k0). For n=k+2,k0=1 this is always R3. With k>=2,1<s<=k,0<t<=2k, set U in G(k+2,k-1),V in G(k+2,k). The analogue of S lies in A(k+2,k-1), of dimension3k. The plane-direction space has dimension2k. The same equations with6 replaced by3k and4 by2k give

  dim S >= k+t.

Its (k-1)-planes meet F in dimension at least sigma-1. Héra's general theorem with c=ceil(sigma), so ceil(sigma-1)=c-1, gives

  dim F >= sigma-1 + [k+t-3(k-c)]/c
         = sigma+2-(2k-t)/c.

Choose sigma<s approaching s from below while ceil(sigma)=ceil(s), including when s is an integer. The resulting parameter formula is

  s+2-(2k-t)/ceil(s).

This is an instance of BD's same proof with the new source input. It is not a second selected family, a novel dimension-raising construction, or an author nominee. The n=4,k=2 formula is its clearest concrete case. Constants depend on the fixed dimension, slack exponents, local charts, source C_epsilon and localized slice mass; no uniform constant at zero slack is asserted.

## Contribution accounting

All operations above have been paid by K3, BD's actual flag/cover argument, Héra's counting proof, and established slicing/measure selection. Correcting the placement of Jensen's power, preserving an epsilon sign, avoiding a falsely common slice direction and adding a cover margin do not create a substantial discovery. They make the strongest known composition explicit. No independent mathematical grade is assigned. The absence of an identified nonroutine operation is the reason for no nomination, not a claim that neighboring research is impossible.
