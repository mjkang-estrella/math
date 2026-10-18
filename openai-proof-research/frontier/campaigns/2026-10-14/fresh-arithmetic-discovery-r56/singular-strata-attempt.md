# Singular strata and the auxiliary construction

This note exposes a second independent obstruction; it does not prove a four-column zero-determinant estimate.

A natural replacement for the source's elliptic quadric is the affine rational normal curve Gamma={(t,t^2,t^3,t^4):t in F_q} in F_q^4. Every four distinct points are affinely independent: the 4x4 minor with rows 1,t,t^2,t^3 is Vandermonde. Translate Gamma and intersect a box of side w; averaging gives a fixed subset S with size s>=w^4/q^3. As in the source, choose w=floor(q/(C H^2)) with C sufficiently large and q>>H^2. This gives s>>q/H^8.

The source's restricted-translation argument extends directly: require ||ma_1||_q>4Hw for 1<=m<=4H. Its excluded probability is at most 4H(8Hw+1)/q, less than 1/2 for sufficiently large fixed C. After a uniform GL4 transformation, a relation among four distinct residues with coefficients of Euclidean norm <=H is impossible. For nonzero coefficient sum use the first-coordinate exclusion; for zero sum use affine independence. Zero residues are excluded by the m=1 case.

With W(A)=(q^4/s)^4 Pr(all four residues belong to the transformed S), the unrestricted affine-group orbit formula and the conditioning cost at most two show W(A)<<1 for four affinely independent columns. For precisely three distinct affinely independent columns (one repeated), the same formula gives W(A)<<q^4/s. This uses transitivity on ordered affine triples, not an unjustified linear-rank hypothesis. For t distinct affinely independent columns the corresponding bound is (q^4/s)^(4-t), up to an absolute constant.

However, the source's zero-determinant proof uses more than these weights. In four columns, pairwise distinct projected points do not imply rational rank three: rational rank two includes four collinear projected points. Even in rank three, the unique primitive null vector can have zero coordinates when three projected points are collinear. Those lower-dimensional degeneracies must be counted or removed before using a null-vector argument that assumes every coordinate is nonzero. The source's three-column inference cannot be reused verbatim.

Here is the issue even in a favorable rank-three subcase, assuming all three-column subsets are independent. Let Lambda have index I=DEF and contain F Z^4. For primitive x let g(x) generate x dot Lambda. Then g|F and the hyperplane lattice Lambda_x has covolume I|x|/g. Four rows of length O(N) spanning that hyperplane have at most

    O(N^12 g(x)^4/(I^4 |x|^4))

choices. To justify this elementary estimate, if such a spanning row tuple exists then all three successive minima of Lambda_x are O(N); a fundamental-parallelepiped count in fixed dimension gives O(N^3/det Lambda_x) choices for each row. Cubing the lattice argument is insufficient; there are four rows and the fourth power must be used.

For R>=h the same congruence count as source section 07 gives

    sum_(primitive x, R<=|x|<2R) g(x)^4 << R^4 I.

Indeed B^j|g is equivalent to Cx=0 mod B^j, whose residue density for j<=f is B^(-j-max(j-b,0)-max(j-e,0)). Weighting by B^(4j) gives a geometric sum with largest exponent f+b+e=log_B I. This controls generic long normals. Pointwise one only has g(x)^4/I<=F^3/(DE)<=h^3.

Now suppose a repeated residue pair has difference delta=e_i-e_j and x mod q is a multiple of delta. There is no additional row congruence beyond x-perpendicularity. Under the favorable nonzero-coordinate assumption, a coordinate outside the pair is a nonzero multiple of q, so R>q/2. The number of such x in a shell is O(R^4/q^3). Combining this count with the pointwise g bound and the three-distinct-column weight gives only

    O(N^12/I^3 * h^3 q^(-3) (q^4/s))
       = O(N^12/I^3 * h^3 q/s).

With the guaranteed s>>q/H^8 this is O(N^12/I^3 * h^3 H^8). Enlarging q does not remove that factor. This is an upper-bound loss, not a proof that the actual sum is that large. It identifies the absent estimate: one needs a joint g-moment for normals constrained to a line modulo q, or a different auxiliary design. The unrestricted R>=h moment does not retain the q^(-3) saving. Counting independent residues modulo h and q is legitimate only with appropriate box-size/error control; R>q/2 does not imply R>=hq.

A primary comparison prevents silently postulating a q^(1+epsilon) auxiliary track. Van de Voorde–Voloch, arXiv:2511.04884v1, introduction and Theorem 1.1, construct 2q+1 points in projective four-space with no four coplanar (when 3 is nonsquare), and report the gap to an upper bound of order q^(3/2). This theorem offers no fixed positive-power gain over q. Its full proof is not used here. Even that possible auxiliary improvement would not resolve the separate digit moment in norm-and-orbit-attempt.md.

Thus the source's zero-determinant module has two genuine new requirements: all lower-rank strata, and the correlated arithmetic estimate in the exceptional-normal stratum. Neither is settled. No conditional reduction is nominated as T191V56.
