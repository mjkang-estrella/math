# Integrated finite-volume reduction

These are prefreeze feasibility derivations, not a frozen author-proof nominee. They retain the strongest closed operations and isolate what is not supplied by them. All pinned operations are stipulated true. Notation U, Gamma and g is exactly the full feasibility question in Note 01.

## 1. Replace the disc-continuity input before changing the scaling

The source's proper Kobayashi distance is obtained from cocompactness. That particular proof is not available here. However, its disc-continuity consequence is available directly from pseudoconvexity of U in C^n, hence Steinness.

Let A:[0,1] x closed(Disk) -> Omega be a continuous family of analytic discs in a smooth ambient chart, all of whose boundaries are in U, and with A_0 wholly in U. Let L be the compact union of their boundary circles. Whenever the whole disc A_t is in U, the maximum principle for every h in O(U) puts A_t(closed(Disk)) inside the holomorphic hull of L in U. That hull is compact in U. The set of such t is open by compactness of a disc and closed by this common hull bound and continuity. It is therefore the full interval.

Consequently, the source's complete H^2 Bishop-disc construction, positive regularization delta=t^2, inverse-function estimate and included normal balls remain applicable. The source's boundary cell, ramification, joint offset limits and independent-peak construction use boundedness and semialgebraicity, not the quotient. Its smoothness step is unnecessary because this question begins with an open domain in C^n. We therefore obtain its good supported point p and all the data used in prop:scaling-limit without assuming cocompactness.

Write the fixed local chart as Phi, delta_t(Z,W)=(sqrt(t)Z,tW), and

    D_t = delta_t^{-1} Phi^{-1}(U intersect Omega),
    R(Z,W) = L Im W - Q(Z),
    O = {R not in F}.

Here L is invertible, F is a closed proper cone, and each connected component D_0 of O is a quadratic epigraph over a nonempty connected open cone. For every E compactly contained in O, E is contained in D_t for small t. Conversely, if R(xi) is in F, then for every t_j down to zero there are excluded xi_j outside D_tj with xi_j -> xi. We retain this exact two-sided assertion; mere convergence of boundary equations is insufficient.

## 2. Finite volume pays ordinary peak recurrence

The source supplies entire h_a with h_a(p)=1 and |h_a(q)| <= exp(-c|q-p|^2) on the closure of U, with a positive c (the source coordinates take c=1). Fix one such peak h. The family h composed with gamma is uniformly bounded and holomorphic. Cauchy estimates on relatively compact coordinate balls make

    u(q) = sup_{gamma in Gamma} |h(gamma q)|^2

locally Lipschitz. It is PSH, because the upper envelope is locally bounded and is already continuous. It is Gamma-invariant by reindexing. It descends to the orbifold quotient and satisfies 0 <= u <= 1.

The exact finite-volume cutoff calculation is already KLW Lemmas 2.1–2.2 (and Pu–Wang Lemmas 2.5–2.6). With chi_R supported in the 2R metric ball, equal to one on the R ball and |grad chi_R| <= 2/R, test weak subharmonicity against chi_R^2 u. Cauchy–Schwarz/Young gives

    integral chi_R^2 |grad u|^2
        <= 4 integral u^2 |grad chi_R|^2
        <= 16 Vol_g(Gamma\U)/R^2 -> 0.

Finite chart groups are handled by averaging tests and dividing both integrals by the group order, exactly as in KLW. The complete quotient metric supplies the cutoffs. Thus u is constant. Since u >= |h|^2 and sup_U |h|=1, u=1. For every fixed q in U there are gamma_j with |h(gamma_j q)| -> 1, hence gamma_j q -> p. The other support functions then tend to 1 on the same sequence by continuity.

This closes simultaneous ORDINARY approach to the selected peak. It does not quantify the normal residuals or the rescaled real-normal coordinates. Lack of an ordinary orbit accumulation point is not the residual obstruction.

## 3. The exact normalization interface

A sufficient input to continue the whole construction is:

    There exist one good supported point and its fixed chart above,
    a component D_0 of O, t_j down to zero, b_j -> b_0 in D_0,
    gamma_j in Gamma, and k_j in a compact subset of U such that

        gamma_j(k_j) = Phi(delta_tj(b_j)).                 (A)

After passage to a subsequence k_j -> k_* in U. The original source supplies (A) with b_j=(0,ia_0) by cocompactness. Here (A) is an UNPROVED sufficient condition, not an added hypothesis in the full feasibility question and not a nominated conditional result. The following calculation establishes that all analytic forward/inverse operations close if (A) is supplied.

Since b_j is bounded and the logarithmic differential of each h_a has no z term, h_a(Phi(delta_tj b_j))=1+O(t_j). For any compact E in U, d_U(q,k_j) is uniformly bounded for q in E. This uses only the local topology and continuity of the finite Kobayashi distance on a bounded connected domain; properness of its balls is unnecessary. Schwarz–Pick for h_a gives

    h_a(gamma_j q)=1+O_E(t_j).

The peak estimate gives |gamma_j q-p|=O_E(sqrt(t_j)). In chart coordinates, expand

    log h_a = i ell_a(w) + O(|z|^2+|z||w|+|w|^2).

The k independent rows ell_a improve w=O_E(sqrt(t_j)) to w=O_E(t_j). Thus

    f_j = delta_tj^{-1} Phi^{-1} gamma_j

is eventually defined near every compact subset of U and locally uniformly bounded. A subsequence converges holomorphically to f:U -> C^n.

## 4. Inverse stability closes the apparent proper-distance gap

Set

    g_j = gamma_j^{-1} Phi delta_tj : D_tj -> U.

The maps are injective and bounded in the fixed Euclidean coordinates of U. Since every compact subset of D_0 is eventually in D_tj, Montel and diagonal extraction give g:D_0 -> closure(U). The varying anchor causes no problem: a fixed ball around b_0 lies in D_tj, boundedness gives equicontinuity there, and g_j(b_j)=k_j. Hence g(b_0)=k_* in U.

Choose a small ball B around b_0 whose image under g has closure in U. On a smaller closed ball, g_j(B) then lies in one compact subset of U. There f_j converges uniformly. The exact identity f_j g_j=id therefore passes to the limit near b_0:

    f g = id near b_0,  so det dg(b_0) != 0.             (1)

Every local Jacobian det dg_j is zero-free. Hurwitz, applied on local complex lines or through the usual several-variable zero-free limit argument, says its limit is either identically zero or zero-free. Connectedness and (1) show det dg is zero-free on all of D_0.

Now fix x in D_0. Normalize source and target coordinates by dg_x and take a small closed ball V about x on which the normalized derivative differs from the identity by less than 1/4. Cauchy estimates and local uniform convergence give the bound 1/2 for g_j for large j. The contraction map solving g_j(v)=y shows that ONE fixed open ball about g(x) is contained in g_j(V), for every sufficiently large j. Since g_j(V) is contained in U, this proves g(x) is in U. No completeness or tautness assertion is being inferred.

For E compactly contained in D_0, g(E) is compactly contained in U, and uniform convergence now places all large g_j(E) in one compact subset of U. Consequently

    f g = id on all of D_0.                              (2)

The same zero-free Jacobian argument applied to f_j and (2) shows that f is locally invertible everywhere on U. At q in U, its local inverse stability gives a fixed ball about f(q) contained in f_j(V_q), hence in D_tj. If R(f(q)) were in F, the source's excluded-point sequence would contradict this ball inclusion. Therefore f(U) is contained in O. It is connected and contains D_0 by (2), so f(U)=D_0. Finally f_j(q) eventually lies in a compact neighborhood of f(q) inside D_0; passing to the limit in g_j f_j(q)=q gives g f=id_U.

This proves the GLOBAL biholomorphism U ~= D_0 under (A), with both image-component and surjectivity issues settled. The local inverse argument is elementary normal-family machinery closely related to the source's own stable-image-ball proof. It is retained as a compatibility repair, not claimed as a substantial new theorem.

## 5. Do not leave a second unpaid symmetry step

The source's triangular change removes the pure holomorphic quadratic terms, giving

    S = {(z,w): Im w - H(z,z) in C},
    ell_a(y)>0 on C,
    ell_a(H(z,z)) >= c |z|^2,

with C a nonempty connected open cone. Its explicit map

    (z,w) -> ((u_1-i)/(u_1+i),...,(u_k-i)/(u_k+i),z/(u_1+i)),
    u_a=ell_a(w),

is a bounded realization in C^n: |z/(u_1+i)| <= 1/(2sqrt(c)). Independence of the ell_a gives its inverse. This step is exactly source 04–05 and requires no quotient compactness once the global equivalence is known.

Here pseudoconvexity pays the conversion from a possibly nonconvex cone to a genuine Siegel domain. S is Stein. Its closed complex submanifold at z=0 is the tube R^k+iC, also Stein; the tube theorem makes C convex. The rotational-disc argument of Vey Proposition 1.1 gives (0,w) in S whenever (z,w) is in S. One can repeat it using the compact holomorphic hull of the circles along a path from a point with z=0, precisely as in part 1 above. Substituting w=i(H(z,z)+y) gives H(z,z)+y in C for every y in C. Replace y by epsilon y and let epsilon tend to zero: H(z,z) is in closure(C). The strict support estimate forces H(z,z)!=0 for z!=0. C contains no affine real line, because otherwise the tube would contain a complex line, incompatible with a bounded realization. Thus H is C-Hermitian and S is a Siegel domain of the first or second kind.

Transport the complete invariant metric and Gamma to the bounded realization. KLW Lemma 3.1 gives a lattice in G=Aut^0(S) and makes G unimodular; freeness is not required. Concretely, the unitary frame bundle has the quotient volume of U because its fibres have probability Haar measure. H=G Gamma acts freely and properly on it. Over a relatively compact slice B, the quotient density factors into Haar measure on (Gamma intersect G)\G times a positive transverse density. Finite total volume makes that Haar quotient finite. Right translation scales its measure by the modular character; its finite nonzero total mass forces that character to be one.

The Vey grading for a Siegel domain is

    g = g_-1 + g_-1/2 + g_0 + g_1/2 + g_1,
    dim g_-1=k, dim g_-1/2=2m,
    dim g_1/2<=2m, dim g_1<=k.

For the Euler field E, unimodularity gives

    0=tr(ad E)=-k-m+(1/2)dim g_1/2+dim g_1.              (3)

Both upper bounds must be attained. Vey's injectivity of (ad A)^2 on g_1 and the evaluation of [A,g_1] at (iy,0) provide all imaginary normal directions. Real translations and Heisenberg fields provide the remaining tangent directions. Thus G acts transitively. The classical symmetry consequence for a unimodular homogeneous bounded domain is the Hano–Koszul–Borel conclusion recalled by Vey on p.479; Pu–Wang use this same graded route, with an additional orthant identification to obtain products of balls. No new final Lie-theoretic operation is claimed. Separate proofs of those foundational classical theorems were not reread; the reduction uses their standard primary-stated interface.

Therefore compact-normalized two-sided scaling, not the finite-volume lattice or final Lie algebra, is the remaining construction in this route. Adding (A), convexity, Kodama's local conditions or HHR to the proposed full question would not be an answer to it.
