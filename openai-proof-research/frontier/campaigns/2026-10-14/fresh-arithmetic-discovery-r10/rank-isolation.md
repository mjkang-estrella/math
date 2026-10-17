# Interior-rank isolation in the Lech complex estimate

Myeongjin Kang; no affiliation. Original prose CC BY 4.0. Frozen author proof for full target AB194, as specified in scope.json. This is not an independent proof verdict or contribution acceptance. The pinned source is stipulated true. The contribution question remains whether the wider-window rank isolation is substantial or only a technical strengthening of its polynomial choice. No campaign count changes here.

## Source interface

Use the complete hypotheses of Theorem `thm:complex` in the pinned Lech manuscript. Thus C is a commutative ring, I=(z_1,...,z_h), h>=1, and lambda is an additive nonnegative extended length on I-power-torsion modules. It vanishes on zero and preserves length zero under direct sums and filtered colimits killed by a common power of I. For every a>=1,

- mu=lambda(C/I) is positive and finite;
- lambda(C/(z_1^a,...,z_h^a))=a^h mu;
- all positive Koszul homology on that list has length zero.

F is finite free in degrees 0,...,h, contractible locally outside V(I), with ranks b_j, alternating rank zero, and differential entries in I^s, s>=1. No Noetherian hypothesis on C is added.

Take the source's blowup Y, invertible ideal L=I O_Y, exceptional divisor E, and divided complex G_j=L^(−js) tensor F_j. The following lower operations, with their actual proof bodies read, are imported unchanged:

1. `lem:acyclicity`: lambda H_j(F)=0 for j>0 and lambda H_0(F) is finite.
2. `lem:complex-graded-comparison`: cohomology on E agrees, modulo length zero, with the corresponding projective-space cohomology.
3. `lem:complex-twist-maps`: sufficiently separated twist maps vanish on hyperhomology; these hyperhomology groups have finite length.
4. `lem:complex-euler-comparison`: for every integral vector bundle V used there, chi_lambda(F_Y tensor V)=rank(V) lambda H_0(F).
5. `lem:complex-root-bundle`: any strictly decreasing integer roots r_1>...>r_(h−1) give a bundle V of rank (h−1)! whose twist V(a) has cohomology only in degree #{j:r_j>a}, or has zero cohomology when a is a root; its Euler polynomial is product_j(a−r_j). These properties hold after the required arbitrary base changes, modulo length zero on E.

The source chose roots to isolate b_0. The argument below changes that choice and verifies the required sign anew.

## Wider sufficient root windows

Assume

`−(j+1)s < r_j < −(j−1)s`, for `1<=j<=h−1`.

Put D=G tensor V. For an exceptional layer with index l>=0, the term in complex degree k has sheaf cohomology in degree

`v(l−ks)=#{j:r_j>l−ks}`.

If k<h−1, every j>=k+1 has r_j<−(j−1)s<=−ks<=l−ks, so v<=k. For k>=h−1 this is automatic. Hence the layer has no negative total homology modulo length zero. The positive-layer filtration of D/D(M), followed by the zero twist map from D(M) to D for sufficiently large M, gives lambda H_k(Y,D)=0 for k<0.

If l<0 and k>=1, every j<=k−1 satisfies r_j>−(j+1)s>=−ks>l−ks, so v>=k−1. For k=0 the inequality v>=−1 is automatic. Thus a negative layer has no total homology in degrees greater than one. The filtration of D(−M)/D, followed by the zero map from D to D(−M), gives lambda H_k(Y,D)=0 for k>0. This uses exactly the finite-filtration and twist-map interfaces above, with no additional limit interchange.

Therefore chi_lambda(D)=lambda H_0(Y,D)>=0 under these wider windows.

## Cardinal interpolation at an arbitrary homological degree

Fix i in {0,...,h} and define

`H_i(x)=product_{0<=j<=h, j!=i}(x+j)`.

It has degree h, leading coefficient one and h distinct real roots. Let rho_1>...>rho_(h−1) be the roots of H_i'. Rolle's theorem gives one root between each consecutive pair of roots of H_i, hence exactly h−1 simple roots. If 0<i<h, their locations are

- −j<rho_j<−(j−1) for j<i;
- −(i+1)<rho_i<−(i−1);
- −(j+1)<rho_j<−j for j>i.

For i=0 only the last pattern occurs, and for i=h only the first occurs. In every case

`−(j+1)<rho_j<−(j−1)`.

Choose integer roots r_j with |r_j−s rho_j|<=1. For sufficiently large s they remain distinct and satisfy the wider windows. Since i ranges over a finite set, one threshold works for all i, depending only on h.

The comparison of F_Y tensor V with G tensor V through the finite exceptional layers gives

`0 <= (h−1)! lambda H_0(F) + mu sum_(j=0)^h (−1)^j b_j sum_(l=−js)^(−1) product_(a=1)^(h−1)(l−r_a)`.

The j=0 inner sum is zero. Set P_i=H_i'/h, which is monic of degree h−1. Uniform polynomial approximation under the bounded rounding errors and the elementary Riemann-sum estimate on [−h,0] give

`s^(−h) sum_(l=−js)^(−1) product_a(l−r_a) = (H_i(0)−H_i(−j))/h + O_h(1/s)`.

The estimate is uniform in j and i. At the nodes, H_i(−j)=0 for j!=i, whereas

`H_i(−i)=(−1)^i i!(h−i)!`.

Using the zero alternating rank, the leading weighted sum is exactly

`sum_j (−1)^j b_j (H_i(0)−H_i(−j))/h = −b_i i!(h−i)!/h`.

Consequently, for a constant C_h depending only on h,

`lambda H_0(F) >= mu s^h [b_i/binom(h,i) − (C_h/s) sum_j b_j]`.

This holds simultaneously for all i. Increasing C_h to cover the finite small-s range makes the right side nonpositive there, so the assertion holds for every s>=1. For h=1 the empty-product construction gives the same formula directly, with b_0=b_1 from alternating rank zero.

## Consequence for every complete ring of characteristic p

Full statement AB194: for every prime p, every nonzero complete Noetherian local ring (R,m,k) of characteristic p and dimension d>=0, and every complex F of finite free R-modules in degrees 0,...,d with finite-length homology and H_0(F)!=0,

`binom(d,i) chi_infty^R(F) >= e(R) beta_i^R(F)` for every `0<=i<=d`.

Explicitly, chi_infty^R(F)=lim_(n→infinity) p^(−nd) sum_j (−1)^j length_R H_j(Phi_R^n F), where Phi_R^n raises every differential-matrix entry to its p^n-th power. Its existence is an imported source fact. Also beta_i^R(F)=dim_k H_i(k tensor_R F), equivalently the dimension of derived Tor_i^R(k,F). There are no reducedness, domain, Cohen–Macaulay, perfection, F-finiteness, standard-grading, or residue-field-size assumptions.

For d=0, F consists only of F_0 and the assertion is the identity rank(F_0) length(R)=beta_0 e(R). For d>0, split off contractible summands to make F minimal, so b_i=beta_i(F).

First suppose R is a domain with algebraically closed residue field. Choose a parameter reduction I of m and c with m^q contained in I^(q−c). The source `thm:length-inputs`, `lem:perfection-finite-length`, and the Frobenius-homology/Dutta comparison in its complete characteristic-p section give, for q=p^n,

`lambda H_0(R_perf tensor Phi_R^n F) = q^d chi_infty^R(F)`.

The extended complex satisfies the abstract hypotheses with mu=e(R), depth s=q−c, unchanged ranks b_i and alternating rank zero. The latter follows by localizing the original short complex at the fraction field. The widened-root estimate gives

`q^d chi_infty^R(F) >= e(R)(q−c)^d [b_i/binom(d,i) − C_d sum_j b_j/(q−c)]`.

Divide by q^d and let q tend to infinity. This proves the assertion for that domain case.

For arbitrary complete R and residue field, use the source's complete flat local residue extension R→S with n=mS, algebraically closed residue field, unchanged dimension and multiplicity. The source's differential-matrix and length comparison preserves Dutta multiplicity; minimality and all b_i are preserved as well. A finite prime filtration of S decomposes the Euler characteristic of each Frobenius pullback. Its factors of dimension less than d contribute O(q^t), t<d, by the exact Frobenius-homology estimate already used in the source. Each top-dimensional factor D=S/P is a complete domain, and D tensor F remains a minimal short complex with the same b_i: localized contractions persist, and H_0 is nonzero by Nakayama. Thus the domain estimate applies to each factor. After division by q^d, taking the limit and summing with the filtration repetitions gives

`chi_infty^R(F) >= [b_i/binom(d,i)] sum_(top factors D) e(D) = [b_i/binom(d,i)] e(R)`.

The same filtration works for every i. These residue-extension/component operations are already paid by the pinned source; only the interior-rank isolation above is the prospective extra operation.

## Closest primary comparison and limits

Iyengar–Ma–Walker, arXiv:2104.10140v2, Theorem 3 / Corollary 7.2 gives these all-Betti inequalities for localizations of standard graded algebras over positive-characteristic fields. Theorem 7.1 and its complete proof construct the required point using the projective scheme of the graded algebra, finite linear projection, product-projective-space sheaves and Frobenius. Theorem 5.16 proves the corresponding general statement conditional on a lim Ulrich point: two computations of Koszul homology identify beta_i and bound it by binom(d,i) times the intersection pairing. Its full proof was read. The argument here does not assert such a point; it changes the source's integral root-bundle test while keeping its blowup and normalized-length comparisons.

This does not prove the all-characteristic IMW Dutta conjecture. It does not replace Dutta multiplicity by ordinary Euler characteristic on arbitrary rings. It does not provide a proof that every local ring has a lim Ulrich sequence. No independent review or worldwide novelty claim is made. The mathematical proof and the campaign contribution question must be judged separately.

The later comparisons, exact reading limits, and prior-developed-chain screen are in reading-and-comparison.md. No unpaid mathematical step is identified by the author relative to these stipulated interfaces; this assertion awaits independent review.
