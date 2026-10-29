# Complete obstructions for failed routes — not a source resolution

All coordinates below are barycentric in the standard simplex Δ_(m-1). Any nondegenerate simplex is affinely equivalent to it; an affine change multiplies all Vandermonde determinants in one fixed basis by a common nonzero basis-change determinant. Thus determinant RATIOS and comparison signs are preserved. We use the literal source F4, whose unisolvence is given in the source.

## 1. Why face-preserving perturbations cannot help

Use the homogeneous degree4 barycentric monomials λ^α, |α|=4, as basis. They form a basis of polynomials of degree<=4 on sumλ=1: homogenization gives spanning, and their number is N=binomial(m+3,4). Group columns by the support S of α; for |S|=s there are binomial(3,s-1) positive compositions. Group source nodes by their exact positive-coordinate support. The counts for s=1,2,3,4 are respectively1,3,3,1, agreeing with the column counts. A monomial supported on R vanishes on a node supported on S unless R⊆S. Ordering by support size makes the evaluation matrix block lower triangular, with diagonal blocks indexed by each particular S.

Now permit arbitrary simultaneous perturbations of the nodes assigned to S WITHIN that same face, keeping the number per S. The same triangular zero pattern persists even at boundary coincidences, where the determinant may become zero. The determinant is the product of the local diagonal-block determinants. For s=1 the point is fixed. For s=2 and3, each block is no larger in absolute value than its original block: otherwise install that block's competitors into the known degree4 Fekete configuration on the corresponding triangle, keeping all other blocks fixed. Its determinant would increase, contradicting the published d=2 Fejer property (source Proposition4.1) and Fejer⇒Fekete (Proposition0.6). For s=2 embed the edge in a triangle and leave its other nodes fixed. All other original blocks are nonzero by source unisolvence. For s=4 the block is the scalar ∏_(i∈S)λ_i, at most(1/4)^4 by AM–GM, attained at its original centroid. Therefore the product cannot improve in any dimension. This is a routine restriction of known low-dimensional extremality. It says nothing about configurations changing their face allocation.

## 2. A genuine inward family also fails

Let m>=4. Index four-subsets A⊂{1,...,m} and their nodes c_A=(1_A)/4. The cardinal polynomial at c_A is
L_A(λ)=256∏_(i∈A)λ_i.
Indeed it vanishes on every source node with support<=3 and on every different four-subset centroid, and equals1 at c_A. Its degree is4; uniqueness of interpolation proves it is the literal source cardinal polynomial, without relying on the source's longer edge formulas.

Fix t∈[0,1]. Replace EVERY c_B by z_B=(1-t)c_B+t u, u=(1,...,1)/m, and leave all other source nodes fixed. These are actual simplex points, strictly interior when t>0; at t=1 they coincide. Put a=(1-t)/4, b=t/m. For r=|A∩B|,
M_(A,B)=L_A(z_B)=256(a+b)^r b^(4-r).
Choose the original cardinal basis for the FULL N-point Vandermonde. Its original matrix is identity. The unchanged rows give an identity block and zero block, so the new full determinant ratio is det M, even though the moved rows can have nonzero entries at other cardinal polynomials. This closes the realization bridge from the small submatrix to the literal full Vandermonde.

Let W_j(A,J)=1 if the j-subset J is contained in A, and0 otherwise, including j=0 and the empty set. Then
(W_j W_j^T)_(A,B)=binomial(|A∩B|,j).
The binomial theorem gives the EXACT identity
M=256 sum_(j=0)^4 a^j b^(4-j) W_j W_j^T.
All coefficients are nonnegative. Thus M is positive semidefinite. Each diagonal equals
D=256(a+b)^4=(1-t+4t/m)^4<=1.
Hadamard's inequality for a positive semidefinite Gram matrix yields
0<=det M<=D^binomial(m,4)<=1.
For m>4 and t>0, D<1, so the determinant strictly decreases. For m=4 the sole centroid is unchanged, and det M=1. No exact counterexample can occur in this entire interior family. This proof is elementary Gram algebra; no originality or separate discovery credit is asserted.

## 3. The tempting weighted-design bridge is invalid

In dimension4, m=5, Bos gives at the global centroid c the value
K=sum_x l_x(c)^2=(80243sqrt5+9298842)/9453125>1.
There are N=binomial(8,4)=70 nodes. In the original cardinal basis, the Gram matrix of the equally weighted source design is I/N. Form the probability measure
μ_e=(1-e) (1/N) sum_x δ_x + e δ_c, 0<e<1.
Writing v=(l_x(c))_x, its Gram matrix is (1-e)I/N+e vv^T. The matrix determinant lemma, or an orthonormal basis starting with v/||v||, proves
 det G(μ_e)/det G(μ_0)=(1-e)^(N-1)(1-e+e N K).
Its derivative at e=0 is N(K-1)>0. Hence μ_0 is not D-optimal among all probability measures, consistently with the published Fejer failure. The checker also gives an exact strict increase at e=10^(-6), using rational bounds on sqrt5.

But μ_e has71 support points (c is not a source node) and unequal weights, whereas Conjecture4.3 compares70 equally weighted nodes through their Vandermonde. The displayed identity supplies no map preserving determinant improvement into that admissible class. In fact the source's Remark0.7 expressly warns that Fekete does not imply Fejer. Thus neither this classical optimal-design bridge nor the published centroid computation refutes the source Fekete claim. No new source result follows.
