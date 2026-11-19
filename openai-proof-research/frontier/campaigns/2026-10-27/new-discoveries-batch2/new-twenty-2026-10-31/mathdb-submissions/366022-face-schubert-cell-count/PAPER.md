# A disconnected all-edge sign class of stabbing lines

## Abstract

An eight-vertex rational polytope in real projective three-space has two lines that meet its interior, avoid the spans of every edge, and give the same strict projective Chow sign vector. They belong to different connected components of the full stabbing complement. The components therefore outnumber the realized sign vectors. This gives a counterexample to Conjecture 3.5 of Seemann and Zaffalon, recorded as MathDB 366022.

## 1. Statement and conventions

Let \(E=\mathbb R^4\). A point of \(\mathbb P(E)\) is the class of a nonzero vector modulo multiplication by a nonzero real scalar, with the quotient topology. A two-dimensional linear subspace \(W\subset E\) determines the projective line \(\mathbb P(W)\). For a full-dimensional projective polytope \(P\), put
\[
D=\{W\in\operatorname{Gr}_{\mathbb R}(2,4):\mathbb P(W)\cap P\ne\varnothing\}
   \setminus\bigcup_{F\text{ an edge of }P}\{W: W\cap\operatorname{span}(F)\ne\{0\}\}.
\]
The span of a face is the linear span of its homogeneous representatives. The cells in question are the connected components of \(D\) with its Grassmannian subspace topology. In Definitions 2.4–2.6 of [1], \(D=P^{[2]}\setminus\mathcal H_P^2\), since the face dimension for \(n=4,k=2\) is one. The sign vectors are those of Setup 2.7 and §2.2, restricted to \(D\), where all entries are strict. The source identifies vectors differing by simultaneous sign reversal.

For ordered representatives \(r,s\) of the endpoints of \(F\) and an ordered row basis \(w_0,w_1\) of \(W\), use \(C_F(W)=\det(w_0,w_1,r,s)\). This vanishes exactly when the two rank-two row spans intersect nontrivially. Write \(q_{ij}(W)\) for the ordered row minors of \(w_0,w_1\), as in [1, §2.1]. The source calls these *dual* coordinates. Its *primal* coordinates \(p_{ij}\) are the minors of a matrix whose kernel is \(W\). In order \(12,13,14,23,24,34\) they can be represented by
\[
p=(q_{34},-q_{24},q_{23},q_{14},-q_{13},q_{12}).
\]
This is the signed complementary-minor convention, with signs given by the parity of the index shuffle. Laplace expansion gives \(\det(w_0,w_1,r,s)=\sum_{i<j}q_{ij}(r,s)p_{ij}(W)\), the Chow form in [1, (1)]. Interchanging the two row blocks has sign \(+1\). A change of the plane basis multiplies all coordinates by the same nonzero determinant. Changing the fixed endpoint choices or order multiplies one coordinate by a fixed nonzero scalar, giving a bijection on sign classes and preserving their fibers.

The real Grassmannian carries the topology from its embedding by the six projective row minors. Any nonzero minor can be used to normalize the corresponding two columns of a basis to the identity. The other entries are then signed ratios of minors, so the projective row minors determine the plane. The minor map lands precisely in the projective classes of nonzero decomposable two-vectors, since such a vector is a wedge of two independent rows. In the \(q_{12}\ne0\) chart the normalized rows are
\[
w_0=(1,0,a,b),\qquad w_1=(0,1,c,d).
\]
Their minors are \((1,c,d,-a,-b,ad-bc)\), and the inverse graph coordinates are \((-q_{23},-q_{24},q_{13},q_{14})/q_{12}\). The forward map is polynomial followed by projectivization. The ratios are continuous on the nonzero-\(q_{12}\) patch, since they are continuous and constant on scalar classes before taking the quotient, whose map restricts to a quotient on the open patch. This gives a homeomorphism between the whole Grassmannian chart and \(\mathbb R^4\).

## 2. The projective polytope and its edge spans

Use \(h(x)=x_1+x_2+x_3+x_4\) and let \(e_i\) be the standard coordinate vectors. Define
\[
\begin{aligned}
u&=(e_1+e_2)/2, &v&=(e_3+e_2)/2,\\
U&=(e_1+e_4)/2, &V&=(e_3+e_4)/2,\\
A&=(3/2,-1,3/2,-1), &B&=(1/8,9/8,1/4,-1/2).
\end{aligned}
\]
In the affine hyperplane \(h=1\), let \(K=\operatorname{conv}\{e_1,e_3,u,v,U,V,A,B\}\). Our projective polytope \(P\) is the image of \(K\). All eight generators have height one. Every nonzero nonnegative combination has positive height and normalizing by height yields a convex combination. Thus \(P\) is exactly the projective image of the nonzero generator cone.

The six nonnegative generators span the convex hull \(K_0=\{x:h(x)=1,\ x_i\ge0,\ x_1+x_3\ge1/2\}\). To prove the reverse inclusion after checking the six generators, fix \(s=x_1+x_3\in[1/2,1]\). The two coordinate pairs with masses \(s\) and \(1-s\) range independently over two segments. At each corner of their product the point is \(s e_i+(1-s)e_j\), for \(i\in\{1,3\}\), \(j\in\{2,4\}\). This lies between \(e_i\) and \((e_i+e_j)/2\). The product is the convex hull of these corners. Strict inequalities in the description of \(K_0\) give an open subset in the height chart, so \(P\) is full-dimensional.

The supporting equations \(x_3=0\) and \(x_1=0\) cut out precisely the triangles \([e_1,u,U]\) and \([e_3,v,V]\). Their sides are edges of \(K\). In particular, \([e_1,u],[e_1,U],[e_3,v],[e_3,V]\) give the coordinate spans \(12,14,23,34\), respectively, where \(ij\) denotes \(\operatorname{span}(e_i,e_j)\). These two triangles also exhibit six of the generators as vertices. The minimum of \(x_4\) singles out \(A\) and the maximum of \(x_2\) singles out \(B\).

We classify the remaining edges by whether both endpoints have \(x_4=0\). Every edge of a polytope is exposed by a linear functional on its affine chart and has generator endpoints. The planar generators form the quadrilateral \(Q=[e_1,e_3,v,u]\) in cyclic order, as is also seen by taking \(x_4=0\) in \(K_0\). The two diagonals contain relative interior points of \(Q\). A supporting functional maximizing at both endpoints of a diagonal must then maximize on all of \(Q\), so a diagonal cannot be an edge. For the other two pairs that need to be excluded, write \(\ell(x)=\sum_i\ell_i x_i\) for a putative supporting functional on \(h=1\).

- If \(\ell\) maximizes at \(e_1,e_3\), then \(\ell_1=\ell_3=M\), its maximum. Evaluation at \(u,U\) gives \(\ell_2,\ell_4\le M\). Since \(\ell(A)-M=(M-\ell_2)+(M-\ell_4)\le0\), all four coefficients equal \(M\).
- If \(\ell\) maximizes at \(u,v\), then \(\ell_1=\ell_3=C,\ \ell_2=D_0\), and the maximum is \((C+D_0)/2\). Evaluation at \(e_1,U\) gives \(C\le D_0\) and \(\ell_4\le D_0\). Since \(\ell(B)-(C+D_0)/2=(D_0-C)/8+(D_0-\ell_4)/2\le0\), all four coefficients equal \(D_0\).

In both cases the functional is constant on the affine chart and exposes no edge. Thus the only edges entirely in \(x_4=0\) are \([e_1,u]\) and \([e_3,v]\). The sign estimate below handles every other edge together. Also, an exposed edge \(F\subset K\) is exactly \(K\cap \operatorname{span}(F)\). Indeed, if \(\ell=m\) exposes \(F\) in \(K\), the linear functional \(\ell-mh\) vanishes on its span. This recovers the edge from its span and identifies the actual edge indices with the spans used for the divisors.

## 3. The two lines meet the interior

Set \(t=1/1000\) and take \(W_\sigma\), \(\sigma=\pm1\), with rows \((1,0,1,\sigma t)\) and \((0,1,\sigma t,t^2/2)\). Their sum is \(z_\sigma=(1,1,1+\sigma t,\sigma t+t^2/2)\). For the positive branch all coordinates are positive and \(2(z_{+,1}+z_{+,3})>h(z_+)>0\). Thus \(z_+/h(z_+)\) lies in the interior of \(K_0\) in \(h=1\).

For the negative branch put \(z=z_-\), \(\delta=-t+t^2/2\in(-t,0)\), and \(y=z+\delta A\). Then \(y_4=0\), the first three coordinates are \(1+3\delta/2,1-\delta,1-t+3\delta/2>0\), and
\[
2(y_1+y_3)>4-8t>3>h(y)=3-3t+t^2>0.
\]
Consequently \(y/h(y)\) is in the relative interior of \(Q\). Any supporting functional for \(K\) there would be constant on the affine plane of \(Q\). On \(h=1\) it would have the form \(\mathrm{constant}+\lambda x_4\). Since \(U\) and \(A\) have opposite \(x_4\) signs, a supporting functional of this form must be constant. A boundary point of a full-dimensional compact convex set has a nonconstant supporting functional, so \(y/h(y)\) is interior to \(K\). As \(z=y-\delta A\), the point \(z/h(z)\) is a convex combination of \(y/h(y)\) and \(A\) with a positive weight on the interior point. Hence it too is interior. Projectivization is a homeomorphism from \(h=1\) to the open projective height patch, so both lines meet the projective interior of \(P\).

## 4. Every edge has the same strict sign on the two lines

In the edge orders of §2, the four determinants on the graph chart are
\[
C_{[e_1,u]}=(ad-bc)/2,\quad C_{[e_1,U]}=-a/2,\quad
C_{[e_3,v]}=-d/2,\quad C_{[e_3,V]}=1/2.
\]
These follow by elimination with the two normalized rows. In particular, at either witness their values in that order are \((-t^2/4,-1/2,-t^2/4,1/2)\).

For any generator pair \(r,s\), the same elimination using the witness rows gives \(C_{[r,s]}(W_\sigma)=\det(Q_\sigma(r),Q_\sigma(s))\), with the indicated endpoint order and
\[
Q_\sigma(x)=(x_3-x_1-\sigma t x_2,\ x_4-\sigma t x_1-t^2x_2/2).
\]
Use \(Q_0(x)=(x_3-x_1,x_4)\) as the limiting map. The four planar generators \(e_1,e_3,u,v\) have nonzero first coordinates \(-1,1,-1/2,1/2\). The four off-plane generators \(U,V,A,B\) have nonzero second coordinates with distinct first-to-second ratios \(-1,1,0,-1/4\). For any distinct pair with at least one off-plane endpoint the limiting determinant is thus nonzero. Both coordinates of every \(Q_0\)-image belong to \(\tfrac18\mathbb Z\) and have absolute value at most one. Each such nonzero determinant has absolute value at least \(1/64\).

Since the generator coordinates have absolute value at most \(3/2\), each coordinate perturbation is at most \(2t\). Each product in the two-by-two determinant changes by at most \(4t+4t^2\), by expanding in the two increments. The determinant changes by at most \(8t+8t^2<1/64\), so its strict sign at either witness is its limiting sign. This covers every off-plane edge. The two planar edges have already been checked explicitly. Thus both witnesses lie in \(D\), with identical strict sign vectors in the normalized row convention.

## 5. Connected components and the count

The edge \([e_3,V]\) forces \(q_{12}\ne0\) everywhere on the arrangement complement. Accordingly \(D\) lies entirely in the single chart of §1 and has its subspace topology there. The selected determinant for this edge is \(1/2\) throughout the chart. Each determinant is continuous and nonzero on \(D\); its strict sign is locally constant. The constant positive edge coordinate prevents a vector and its global reversal from both occurring as normalized chart vectors. Thus equality of projective sign classes on \(D\) is exactly equality of the strict chart vectors.

On the common witness sign fiber the first three displayed determinants force \(ad-bc<0,\ a>0,\ d>0\). It follows that \(bc>ad>0\). In this fiber \(b\) is never zero, so its positive and negative sets are disjoint relatively open sets covering the fiber. The two witnesses have \(b=\pm t\). Any connected set in \(D\) has constant strict signs, and a connected subset of the common fiber cannot meet both sets. The witnesses therefore belong to different connected components, even if one considers the ambient arrangement complement without the stabbing constraint.

The sign map on components is well-defined and surjective, because each realized sign has a representing line. The common witness sign has at least two components. The sign set is finite and nonempty. A surjection onto a finite set with a repeated fiber rules out equality of the two cardinalities, whether or not the domain is finite.

For the usual finite numerical count, the standard projection and finite-component theorems for real semialgebraic sets give that the component count here is finite. In chart coordinates, stabbing is expressed by the existence of real \(\lambda_i\ge0\) with \(\sum_i\lambda_i=1\), \(x=\sum_i\lambda_i g_i\), \(x_3=a x_1+c x_2\), and \(x_4=b x_1+d x_2\), where the \(g_i\) are the eight generators. The arrangement complement adds finitely many polynomial nonvanishing tests. Projection preserves semialgebraicity, and real semialgebraic sets have finitely many connected components. Therefore the number of cells is strictly greater than the number of realized sign vectors. This disproves Conjecture 3.5 for \(n=4,k=2\).

## 6. Checked statement and attribution

The Lean appendix defines the polytope as the image of the nonzero real generator cone, the Grassmannian by projective row minors with the induced topology, the domain by literal projective intersection and all exposed edge spans, and the signs by the source Chow sum modulo global reversal. The theorem `G366022.mathdb_366022_counterexample` gives full dimension and the impossibility of a bijection between the actual component set and the realized sign set on that domain. `literal_cell_count_ne` also gives inequality of their Lean `Nat.card` values. On an infinite type `Nat.card` is zero. The sign type is finite nonempty, and the strict natural-number comparison in `native_finite_cell_count_gt` assumes component finiteness. The ordinary finiteness argument in §5 supplies that hypothesis mathematically. The appendix does not formalize that semialgebraic theorem or compute either exact count.

The ambient four-divisor obstruction and the branch used in §5 precede this convex realization. Mazzucchelli, Pavlov and Wang [2, Example 5.2] analyze the four hyperplanes and report double fibers, including the sign triple used here in row-minor coordinates. Seemann and Zaffalon [1, Example 3.4] present two lines with a common sign on those four divisors of the simplex. The second line misses the simplex, and the other two simplex edge signs distinguish the pair. Their determining-face theorem and their conjecture ask different questions. In the present construction the two additional vertices remove the obstructing planar edges, the uniform sign estimate handles all other actual edges, and both lines stab the interior. The comparison with the related Plücker-space polytopes of Pavlov and Ranestad [3] concerns a different input and conclusion. The proof here uses none of the reported numerical region counts.

The record binding is the retained MathDB 366022 row, UUID `1fed37af-b60a-483e-a73b-e5fe559d218e`, from the dated corpus projection. It matches Conjecture 3.5 in both owned versions of [1]. The retained open label and empty solutions field are historical metadata. The bounded prior comparisons establish attribution of the ambient obstruction and the difference between the inspected examples and the convex realization. They leave global priority and current registry qualification unresolved. The owned registry evidence consists of a dated main ref at `4eaee87548250b2682affda7d05d947c05554bae` (2026-11-17T08:28:51.901Z) and a 373-group catalogue projection (2026-11-14T22:28:25.825Z) with no recorded candidate hit. The exact commits/main and API robots/ref holds and source-specific holds remain operative.

### References

1. Sebastian Seemann and Francesca Zaffalon, *How to stab a polytope*, §2.1 equation (1), Definitions 2.3–2.6, Setup 2.7, Remark 3.3, Example 3.4 and Conjecture 3.5. [arXiv:2412.00551v1](https://arxiv.org/abs/2412.00551v1), [Le Matematiche 80 (2025), 473–493](https://doi.org/10.4418/2025.80.1.20).
2. Elia Mazzucchelli, Dmitrii Pavlov and Kexin Wang, *Hyperplane arrangements in the Grassmannian*, §5, Example 5.2. [arXiv:2409.04288v1](https://arxiv.org/abs/2409.04288v1), [Le Matematiche 80 (2025), 387–408](https://doi.org/10.4418/2025.80.1.16).
3. Dmitrii Pavlov and Kristian Ranestad, arXiv:2503.01652, versions 1 and 2 (related comparison as reported in the independent ordinary review). [arXiv:2503.01652](https://arxiv.org/abs/2503.01652).

[Lean source appendix](LEAN-SOURCE-APPENDIX.md) · [Module and claim crosswalk](CROSSWALK.md)
