# A counterexample to lexicographic Schur duality for polynomial quantum wreath products

## Abstract

The lexicographic construction of Lai and Minets associates an intersection algebra to a polynomial quantum wreath product satisfying (C1) and (C3). Over \(\mathbb Q\), a five-dimensional coefficient algebra and \(d=3\) give a proper inclusion of that algebra into the endomorphism algebra of the prescribed right module. The obstruction is a map from the block for \((3)\) to the regular block for \((1,1,1)\). Its value on the cyclic generator annihilates the generator's right annihilator but lies outside its principal left ideal. We prove this by extracting one coefficient row of a product in a finite skew group algebra and then passing to polynomial coefficients.

## 1. Statement and parameters

In Lai–Minets v3, Conjecture 6.12 uses a polynomial quantum wreath product \(H=B\wr\mathcal H_d\) satisfying (C1) and (C3). For each ordered composition \(\lambda\) of \(d\), let \(S_\lambda\) permute the positions within each consecutive block of \(\lambda\), and let \(L_\lambda\) be the pairs \(i<j\) within those blocks. With multiplication in lexicographic order, (5.7) defines
\[
 K_\lambda=\sum_{g\in S_\lambda}
   \left(\prod_{(i,j)\in L_\lambda,\;g(i)<g(j)}\alpha_{ij}\right)H_g .
\]
The conjecture uses \(C=\bigoplus_\lambda K_\lambda H\) as a right \(H\)-module and the algebra \(\bar S\) with blocks \(K_\lambda H\cap HK_\mu\). The product of \(xK_\mu\) in block \((\lambda,\mu)\) and \(K_\mu y\) in block \((\mu,\nu)\) is \(xK_\mu y\), extended by matrix multiplication. The conclusion imported from Theorem 6.7 includes \(\bar S=\operatorname{End}_H(C)\) under the prescribed action. We prove that this equality fails.

Take \(d=3\) and \(F=\mathbb Q1\oplus\mathbb Qa\oplus\mathbb Qb\oplus\mathbb Qc\oplus\mathbb Qz\). The basis element \(1\) is a unit and \(ab=c\) is the sole nonzero product of two of \(a,b,c,z\). The bilinear multiplication is associative, since any triple product of radical basis elements vanishes in both bracketings. The degrees of \(1,a,b,c,z\) are \(0,1,1,2,1\), respectively, and multiplication preserves total degree. All tensors and place permutations are ordinary, without graded signs.

Set \(B=F[x]\) with central \(x\). Use the flip \(\sigma\) on \(B\otimes B\), \(R=1\), \(\beta=0\), \(S=0\) and \(\rho=0\). The four coefficients \(\Delta^{ij}\) of \(\beta\) are zero. Each is flip invariant and satisfies the weak Frobenius intertwining identity, and the determinant relation \(\Delta_1^{00}\Delta_2^{11}=\Delta_1^{01}\Delta_2^{10}\) is zero on both sides. The twisted Demazure operator for \(\beta=0\) vanishes, and \(S=\Delta^{10}-\Delta^{01}\). The coefficient algebra is finite-dimensional and unital, \(B\) is free over \(\mathbb Q\), and \(R\) is central and flip invariant. These give the polynomial type in Definition 3.7 with the presentation of Definition 2.3.

Choose \(u=a\otimes b-b\otimes a\) and \(\alpha=1+u\). Each term of \(u^2\) contains \(a^2\), \(b^2\), or \(ba\) in a factor, so \(u^2=0\). The flip sends \(u\) to \(-u\) and \(\sigma(\alpha)=\alpha^{-1}\). Thus \(\alpha(\sigma(\alpha)+S)=R\), giving (C1). In \((F\otimes F)[x_2][x_1]\), the polynomial \(x_1-x_2\) is monic in \(x_1\). Either product of \(x_1-x_2\) with a nonzero polynomial has the nonzero leading coefficient of that polynomial. Multiplication by the unit \(\alpha\) preserves regularity on both sides, so \(\alpha(x_1-x_2)+\beta\) gives (C3). The commutator \([\alpha,a\otimes1]=c\otimes a\) is nonzero. In particular the conjecture's omission of (C2) matters. The chosen \((\alpha,\beta)\) is part of the construction, since \(K_\lambda\) depends on it.

## 2. Native presentation and polynomial coordinates

Put \(A=F^{\otimes3}\), \(D=A\rtimes\mathbb Q[S_3]\) and \(H'=A[x_1,x_2,x_3]\rtimes\mathbb Q[S_3]\). Write tensor slot indices on basis elements and act by \(g(a_i)=a_{g(i)}\) and \(g(x_i)=x_{g(i)}\), with the same rule on all other letters. The multiplication is \((f g)(h w)=f\,g(h)\,gw\), with right-to-left permutation composition. The tensor product \(B^{\otimes3}\) identifies with the coefficient algebra \(A[x_1,x_2,x_3]\) by putting the three coefficients and the three powers in their respective slots. The inverse splits each coefficient monomial into its three tensor factors and extends linearly. The analogous two-factor map identifies \(B\otimes B\) with \((F\otimes F)[x_1,x_2]\) and carries the flip to simultaneous exchange of variables and slots.

Sending the native adjacent generators to \(s=(12)\) and \(t=(23)\) satisfies the braid, quadratic \(H_i^2=1\), and wreath \(H_i f=s_i(f)H_i\) relations for every coefficient \(f\). Conversely, adjacent elements with those quadratic and braid relations represent \(S_3\) by its Coxeter presentation. The wreath relations then give covariance for each group element. For any target \(\mathbb Q\)-algebra with a coefficient map and adjacent elements satisfying these relations, the formula \(fg\mapsto c(f)\,g_{\rm target}\) extends uniquely to an algebra map by the skew multiplication formula. The two presentations are inverse on their generators. Thus \(H=H'\), the coefficient inclusion is faithful, and \(H_g=g\). The ordinary skew action on the polynomial coefficient algebra is also faithful. Given a nonzero \(\sum_g f_g g\), choose \(M\) larger than every exponent in the finitely many coefficient supports. On \(x_2^M x_3^{2M}\), the terms \(f_g g(x_2^M x_3^{2M})\) have mutually disjoint exponent boxes, so a nonzero coefficient survives.

Each element of \(H\) has unique right polynomial form \(\sum_m d_m x^m\), \(d_m\in D\). This follows from \(x^m g=g\,g^{-1}(x^m)\), which bijectively reindexes the exponents in each permutation component. For any \(K\in D\), its right annihilator in \(H\) consists exactly of the polynomials all of whose \(d_m\) belong to \(\operatorname{Ann}_{r,D}(K)=\{h:Kh=0\}\). Evaluation at \(x_1=x_2=x_3=0\) is an algebra retraction \(H\to D\), as it commutes with the place action.

## 3. The six rows and the missing value

The compositions are \((3),(2,1),(1,2),(1,1,1)\). Write \(\omega=(1,1,1)\), \(\mu=(3)\), and \(K=K_\mu\). In this order the parabolics are \(S_3,\{1,s\},\{1,t\},\{1\}\) and the allowed pairs are \((12,13,23),(12),(23),()\). In particular \(K_\omega=1\). Set \(U=u_{12},V=u_{13},W=u_{23}\), where \(u_{ij}=a_i b_j-b_i a_j\). The following table gives the left coefficient of each permutation in \(K\), using the displayed inversions \(g(i)>g(j)\) and the indicated order of multiplication.

| Permutation | One-line form | Non-inverted pairs | Left coefficient |
|---|---|---|---|
| \(1\) | \(123\) | \(12,13,23\) | \((1+U)(1+V)(1+W)\) |
| \(s\) | \(213\) | \(13,23\) | \((1+V)(1+W)\) |
| \(t\) | \(132\) | \(12,13\) | \((1+U)(1+V)\) |
| \(r=st\) | \(231\) | \(12\) | \(1+U\) |
| \(\ell=ts\) | \(312\) | \(23\) | \(1+W\) |
| \(j=sts\) | \(321\) | none | \(1\) |

Put \(G=\sum_{g\in S_3}g\) and \(Z=z\otimes z\otimes z\). The degree-zero part of \(K\) is \(G\), and all nonzero degrees of \(K\) are even. Denote by the \(Z\)-row the \(\mathbb Q[S_3]\) coefficient obtained by reading the coefficient of \(Z\) in every tensor expansion. In \(dK\), \(d\in D\), the \(Z\)-row comes entirely from \(dG\). Every positive-degree coefficient of \(K\) is a sum of basis tensors with \(a,b\) or \(c\) in some slot. This property survives place permutation. A factor with any of those letters on the right cannot give \(z\) in that slot. The \(Z\)-row of \(dG\) is constant across \(S_3\), by reindexing the permutation multiplying each term of \(d\). Also \(Z\) kills every positive-degree coefficient by left multiplication and is fixed by the place action.

Let \(Kh=0\) in \(D\), and write \(h_n,K_n\) for the degree-\(n\) parts. Degree two gives \(Gh_2+K_2h_0=0\). Left multiplication by \(1-s\) eliminates \(Gh_2\). In \(K_2\), the \(a_1b_2\)-row is \(1+t+r\), from the appearances of \(U\) in the table. The action of \(s\) sends \(U\) to \(-U\) and swaps \(V,W\). The row in \((1-s)K_2\) is therefore
\[
 g_*=(1+s)(1+t+r)=1+s+2t+2r.
\]
Here \(st=r\) and \(sr=t\). Since \(h_0\in\mathbb Q[S_3]\), extraction commutes with multiplication by \(h_0\) on the right. Hence \(g_*h_0=0\). It follows that \(y=Zg_*\) satisfies \(yh=0\), since multiplying by \(Z\) kills all higher-degree terms of \(g_*h\). Its \(Z\)-row has coefficient one at \(1\) and zero at \(j\), so \(y\notin DK\).

The right polynomial coordinates imply \(y\operatorname{Ann}_{r,H}(K)=0\). If \(y\) were in \(HK\), the retraction to \(D\) would imply \(y\in DK\). Thus the finite calculation yields the same obstruction over the prescribed polynomial algebra.

## 4. The strict inclusion

For any \(\lambda,\nu\), an intersection element \(q\in K_\lambda H\cap HK_\nu\) represented as \(q=xK_\nu\) acts by \(K_\nu v\mapsto qv=x(K_\nu v)\). The value is independent of both choices of representative and lies in \(K_\lambda H\). For a composable block with generator value \(K_\nu w\), the composite has generator value \(xK_\nu w\), exactly the prescribed product. On the diagonal \(K_\lambda\) acts as the identity. Evaluating on each cyclic generator and projecting to each output summand recovers all the blocks, giving a unital injective comparison into \(\operatorname{End}_H(C)\).

In the block from \(K_\mu H\) to \(K_\omega H=H\), define \(T(Kv)=yv\). If \(Kv=Kv'\), then \(v-v'\) belongs to \(\operatorname{Ann}_{r,H}(K)\), so \(T\) is well-defined. The formula makes \(T\) additive and right \(H\)-linear. Put \(T\) in that block and zero elsewhere to obtain a right \(H\)-linear endomorphism of the four-summand \(C\). The generator value is \(y\notin HK\). Every image of the prescribed comparison has its generator value in \(HK\) in that block. This proves strict inclusion and refutes the conjunction imported by the conjecture.

The regular summand also determines the reverse centralizer. An additive endomorphism commuting with the intersection algebra preserves summands by the diagonal projections. Let \(h\) be its value on \(1\) in the regular summand. For each \(m\in K_\lambda H\) the intersection action includes \(H\to K_\lambda H,\ v\mapsto mv\). Commutation gives the value \(mh\) on \(m\), and conversely right multiplications commute with the intersection action. With ordinary composition their image represents \(H^{\mathrm{op}}\). The regular corner is \(H\) via the block \((\omega,\omega)\), with its usual idempotent functor on left modules. The counterexample concerns the other centralizer equality.

## 5. The cycle convention in Example 6.1

Example 6.1 in v3 swaps the cycle coefficients of \(st,ts\) relative to (5.7) with the displayed functional convention. Using inversions of \(g^{-1}\) gives exactly this swap. In the example's central regime \(\alpha_{23}\alpha_{13}\) may also be written in lexicographic order. In the noncentral construction we keep lexicographic order and examine the inverse convention only as a separate ordinary check.

For the swapped-cycle \(K\), let \(q=\frac16\sum_g\operatorname{sgn}(g)g\). Then \(gq=qg=\operatorname{sgn}(g)q\). If \(Kh=0\), write \(hq=fq\) with \(f\in A\) (unique by the identity coefficient). Its degree-zero component \(f_0\) is the sign character of \(h_0\). Suppose \(f_0\ne0\) and divide by it so that \(f_0=1\). In \(Kfq=0\), the degree-zero group row gives the alternating operator \(T_0(v)=\sum_g\operatorname{sgn}(g)g(v)\) on each homogeneous component of \(f\). The signed group rows for \(U,V,W\) in \(K_2\) are \(1-t+\ell,\ 1-t-s,\ 1-s+r\). Their values on \(1\) give \(U-V+W\). The coefficient of \(q\) in degree four of \(Kq\) is \(UV+UW+VW-UV-VW=UW=b_1c_2a_3\), by \(ab=c\).

Write \(x_{ij}\) for the \(a_i b_j\) coefficient of \(f_2\) and \(C_i\) for its single-\(c_i\) coefficient. At \(a_1b_2\) the degree-two equation is
\[
 L=x_{12}-x_{21}-x_{13}+x_{31}+x_{23}-x_{32}=-1.
\]
For degree four, sum the two coefficient equations at \(b_1c_3a_2\) and \(b_3c_1a_2\). The \(T_0(f_4)\) terms cancel under \((13)\), and \(UW\) has zero coefficient at both. The terms from \(K_2\) acting on \(f_2 q\) are as follows.

| Output | From two letters in \(f_2\) | From one \(c\) in \(f_2\) |
|---|---|---|
| \(b_1c_3a_2\) | \(-x_{23}+x_{32}+x_{13}\) | \(-C_3+C_2-C_1\) |
| \(b_3c_1a_2\) | \(x_{21}-x_{31}-x_{12}\) | \(C_1-C_2+C_3\) |

Indeed, the first row uses \(-b_1a_3\) in \(V\) against \(a_2b_3\) and \(-b_1a_2\) in \(U\) against \(c_3\). The second uses \(a_1b_3\) in \(V\) against \(b_1a_2\) and \(a_2b_3\) in \(W\) against \(c_1\). Pulling those input indices back along each signed permutation gives the indicated coefficients. These are the only products because either \(c\) is formed by \(ab\) in its slot or it is already present in a slot disjoint from the two letters of the left factor. The sum forces \(-L=0\), a contradiction. Hence \(f_0=0\), \(qh_0=0\), and \(Zq\) annihilates the right annihilator of the swapped-cycle \(K\). The \(Z\)-row is nonconstant. The same polynomial extension and block argument apply.

## 6. Source and formal scope

The retained MathDB 366949 statement and the captured page payload agree literally, including blank displays. The references in those displays are identified by the owned primary source. The operative version is Chun-Ju Lai and Alexandre Minets, *Schurification of polynomial quantum wreath products*, arXiv:2502.02108v3, Conjecture 6.12, p. 21. Its inputs are (C1), (C3), and (5.7), with Theorem 6.7 on pp. 18–19 providing the conclusion. The v1 counterpart is Conjecture 5.14, pp. 22–23, with (4.9), p. 14, and Theorem 5.9, pp. 20–21. The construction in both versions uses the chosen admissible pair and the same lexicographic block product. The counterexample supplies a map for these definitions and needs no convolution identification beyond the conjecture's stated construction.

The companion [exact Lean appendix](LEAN-SOURCE-APPENDIX.md) contains the 19 sealed modules. The [appendix crosswalk](APPENDIX-CROSSWALK.json) gives every payload's half-open byte interval, inclusive lines, SHA-256, import edges, and compile and checker labels. The finite coordinate model and witness are in Rule, Model, Coords, NativeK, Certificate, TensorBinding and FiniteCore. PolyModel, PolyLift and PolyBinding provide the polynomial extension. PresentationBase, NativePresentation, TensorPolynomial, Admissibility, SkewOperators and FixedPair give the presentation, polynomial data, faithful ordinary action and native coefficient binding. EndComparison, SchurAlgebra and Endpoint give the intersection action and its failure on the literal direct sum. The endpoint is \(\texttt{PolySkew.MathDB366949_counterexample}\). ReplayAudit and ReplayInventory are separately authored checks outside the exact appendix, including the expanded proposition and the transitive axiom inventory.

The extracted replay covers the displayed inversion convention and the prescribed comparison. Section 5 and the positive assertions about the other centralizer, corner and functor in Section 4 are ordinary arguments. The producer's sealed hand proof and a separately owned independent hand review are distinct evidence. This manuscript was assembled and checked within the replay lane. Its assembled prose has received no separate manuscript review. The formal checks trust the pinned Lean distribution and prebuilt upstream oleans; they rebuild and separately kernel-check the 19 lane modules. They do not identify a theorem of Lean with source prose mechanically. The mathematical contribution is an explicit noncentral admissible pair and a missing endomorphism for its exact lexicographic generator. Priority, registry coverage and acceptance are outside this offline pass.

[Lai–Minets v3](https://arxiv.org/pdf/2502.02108v3) · [Lai–Minets v1](https://arxiv.org/pdf/2502.02108v1) · [MathDB 366949](https://mathdb.com/p/366949/lexicographic-quasi-idempotent-schur-duality-for-polynomial)
