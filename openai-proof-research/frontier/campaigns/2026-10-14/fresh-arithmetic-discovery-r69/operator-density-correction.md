# Correction with small operator density and arbitrary total mass

Author proof development; not an independent gate. This note extends the r67 correction estimates in a different norm. It can be applied to the enlarged cubic of high-space-completion.md. It does not remove that note's exact-B and small-D hypotheses for the original tensor, and therefore does not prove the frozen global target.

For a fully symmetric cubic T write B=JJ*, with J here the multiplication flattening V tensor V -> V (equivalently B=sum Xr²). Put beta_2=||B−I||F, beta_inf=||B−I||op, a=||A||HS. Write eta(A) for the maximum operator norm of all one-versus-three and two-versus-two flattenings of A, including all permutations. Thus eta<=a, but we do not assume a small. Constants below are deliberately conservative.

## 1. Tensor contraction bounds

The following elementary bounds are useful because they distinguish total mass from density.

If a four-tensor A has flattening maximum eta and total norm a, any contraction of two copies along two indices, leaving four free indices, has total norm <=eta*a and every flattening norm <=eta². For the natural two-versus-two cut this is matrix multiplication. For a crossed cut, regard the two contracted indices as the Kraus label: row and column Grams of the resulting matrix families are bounded by the one-versus-three Gram of A, hence by eta²; elementary-operator Cauchy–Schwarz gives the bound. For a one-versus-three cut fix its singleton unit vector, apply the two-versus-two map of the other copy, and use the one-versus-three bound on the fixed copy. Permuting indices before the argument covers all cuts. The HS estimate uses the natural multiplication cut and invariance of total norm under permutations.

Similarly, if H is a fully symmetric cubic with every mode-flattening norm <=h and total norm s, a contraction of two copies along one index has HS norm <=h*s and every four-tensor flattening norm <=h². The crossed cuts use the slice row Gram B(H)<=h²I. These statements are bounds on linear maps on full tensor coefficient spaces, not estimates only for decomposable input vectors.

The exact crossed factorization, with all row/column spaces and singleton Gram indices, is expanded in crossed-contraction.md. Its accompanying exact-integer diagnostic checks Q=RC, RR*=Gram_i(A) tensor I, and C*C=I tensor Gram_l(F) for both equal and permuted factor tensors.

## 2. Exact-B correction

Assume B=I. Use exactly the Hochschild homotopy and signs of r67/associativity-correction.md. Let H=hA and U=T+H. The same contractions give

  ||H||HS<=a,  ||H||mode-op<=eta.

Indeed each mode flattening of H is a product of the isometric multiplication flattening and a two-versus-two flattening of A; H is symmetric by the r67 triple-trace identity. The two error terms Q1,Q2 in the homotopy identity each contract two copies of A along two indices. Therefore the bounds in section1 and A(U)=Q1+Q2+A(H) give

  a(U)<=4eta*a,    eta(A(U))<=4eta².                   (1)

The exact Gram identity remains

  B(U)−I=−2D+Gram(H).

The one-versus-three Gram of A is 2D. Thus ||D||op<=eta²/2 and ||D||F<=eta*a/2. Likewise Gram(H) has operator norm <=eta² and Frobenius norm <=eta*a. Consequently

  beta_inf(U)<=2eta²,    beta_2(U)<=2eta*a.            (2)

Unlike an assertion that D small controls all flattenings, (1) explicitly assumes all flattenings small. The simplex obstruction therefore does not contradict (1).

## 3. Joint normalization in an operator ball

Here beta_inf and eta are small, while beta_2 and a may be arbitrarily large. Write b=||B||op<=1.1. Put F_rs=sum_t T_rst Xt and E_rs=XrXs−F_rs. The E family is a permutation of the associator, so its row and column Grams are bounded by eta²I. The F row and column Grams are bounded by b²I. Moreover

  sum_rs F_rs Y F_rs* = sum_tu B_tu Xt Y Xu.

The difference of this map from K(Y)=sum_t Xt Y Xt has cb norm <=b beta_inf. Expanding the E terms therefore yields

  ||K²−K||cb <=2b eta+eta²+b beta_inf
             <=3eta+2beta_inf=:q.                    (3)

For q small the binomial near-projection formula of high-space-completion.md applies, with ||K||cb=b, and yields a projection Pi0 satisfying

  ||Pi0−K||cb<=16q,  ||Pi0||cb<=b+16q.

For the congruence T_P=T(P.,P.,P.), P=I+E symmetric, the derivative of its Gram at E=0 is

  L(E)=EB+BE+4K(E).

On symmetric matrices 2I+4Pi0 has inverse (1/2)I−(1/3)Pi0. Equation(3) and beta_inf small show ||L^(-1)||_(op->op)<=2 by the Neumann series. This inverse preserves symmetric matrices. Separately S=J*J is positive and S−K is a two-versus-two reshuffling of A, so K>=−eta on the matrix HS space. It follows that L>=2(1−beta_inf)−4eta>=1 and

  ||L^(-1)||_(F->F)<=1.                               (4)

These are distinct inverse bounds; neither is inferred from the other.

For G(E)=B(T_(I+E)), ||E||op<=0.1, the mode-action proof from r67 gives

  ||D²G(E)[H,K]||op<=64||H||op||K||op,
  ||D²G(E)[H,K]||F <=64||H||op||K||F.                  (5)

To verify the mixed bound, every differentiated tensor term has one H mode factor bounded in operator norm and one K mode factor bounded using tr(K² B)<=b||K||F². The remaining factors have norm <=1.1. The Gram product terms use a flattening operator norm on the H factor and a total HS norm on the K factor. Counting the two Gram terms and six second tensor derivatives gives the bound 30(1.1)^4 b<64. No use of ||T||HS is made.

Solve E=−L^(-1)(G(0)−I+G(E)−G(0)−L(E)). For beta_inf+eta<=10^(-8), (3)–(5) make this a contraction on the symmetric operator ball ||E||op<=4beta_inf. The ball is complete in each finite dimension; the constants are dimension-free. The mixed remainder bound and (4) at the resulting fixed point give

  ||E||op<=4beta_inf,  ||E||F<=4beta_2.                (6)

For example the mixed remainder is <=32||E||op||E||F and is absorbed on the left. Thus T_N=T_(I+E) has exact Gram I and

  ||T_N−T||HS<=16beta_2,
  ||T_N−T||mode-op<=16beta_inf.                        (7)

Expanding the two quadratic products defining the associator, with one factor controlled by its mode norm, gives the additional bounds

  a(T_N)<=a+100beta_2,
  eta(A(T_N))<=eta+100beta_inf.                        (8)

For clarity, each linear term is bounded by sqrt(b) times the corresponding norm of T_N−T, there are four such terms, and the two quadratic terms cost at most twice the product of its mode norm and its total norm (or twice its squared mode norm). With (7) and the stated small beta_inf these constants are below100.

## 4. Convergence and the exact zero set

Start with beta_inf+eta<=10^(-12), without any bound on beta_2 or a. Normalize once by section3. This costs <=16beta_2 and produces exact B=I, with

  a0<=a+100beta_2,  eta0<=eta+100beta_inf<10^(-9).

Apply section2 and then normalize again. Equations(1),(2),(7),(8) give

  eta_next<=204eta²,
  a_next<=204eta*a,
  ||T_next−T||HS<=a+32eta*a<=2a.

In particular eta and a decrease geometrically. The sum of displacements is <=4a0, and the limit has B=I and A=0. Exact associativity means the real symmetric slices commute; simultaneous orthogonal diagonalization and full cubic symmetry force only diagonal cubic coefficients. B=I makes every such coefficient +1 or −1, and changing the corresponding basis vector's sign gives a unit orthodeco tensor. This last classification is also the exact classical odeco characterization already credited in r67.

We obtain the supporting quantitative statement

  dist(T,O_m)<=416beta_2+4a                            (9)

whenever beta_inf+eta<=10^(-12), in every dimension and with arbitrary total residual. This is an author derivation for further checking, not an independent proof verdict.

## 5. Application boundary

By equations(11),(13),(14) of high-space-completion.md, its enlarged sigma meets the operator hypotheses for sufficiently small absolute d. Equation(9) then gives dist(sigma,O_(m+r))²<=constant*C. Transferring this result back to the original m-dimensional cubic requires the explicit frame-compression comparison, to be recorded separately.

Even after that transfer, the conclusion concerns original tensors with exact B=I and sufficiently small ||D||op only. The frozen T101G69 theorem allows B<=2I and arbitrary errors. The two initial reduction obligations identified in high-space-completion.md remain unresolved. No stronger conclusion, full entropy proof, nomination, or acceptance is asserted.
