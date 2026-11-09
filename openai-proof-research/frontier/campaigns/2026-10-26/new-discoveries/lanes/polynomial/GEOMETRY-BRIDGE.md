# Supporting exact taxicab geometry bridge

This is a standalone supporting module for the parent's scalar 3/2 argument, not a complete newly counted discovery. Namespace: `TaxicabGeometry`; source: `formal/TaxicabGeometry.lean`.

`norm1 (x,y)=|x|+|y|` is explicit. The module never uses the default norm on a product, which would be the maximum norm. `lineDistance a b c P` is the source's equation (5), `|a Px+b Py+c|/max(|a|,|b|)`. `sideDistance P B C` uses actual supporting-line coefficients `(By−Cy,Cx−Bx,Bx Cy−Cx By)`.

The principal integration theorem is `triangle_side_bounds`. It assumes pairwise-distinct vertices, nonnegative barycentric coefficients summing to one, and the exact vector identity `P=λa • A+λb • B+λc • C`. It proves:

- nonnegative values of all three source side distances;
- `rA≤min(norm1(B−P),norm1(C−P))`, and the two cyclic analogues;
- `(1−λa) rA≤λa norm1(A−P)`, and the two cyclic analogues.

Thus the theorem supplies exactly the hypotheses of a scalar weighted lemma and requires no vertex-distance strict-positivity assumption. It also works for nonnegative, rather than strictly positive, weights; the original interior-point case is included.

The proof uses the direct coordinate bound `|a x+b y|≤max(|a|,|b|)(|x|+|y|)`, actual vanishing of the side functional at both endpoints, and its barycentric affine identity. Both endpoint bounds and the weighted opposite-side bound are proved, including positivity of every genuine line denominator from distinct endpoints. All cyclic permutations and the needed coordinate ordering are explicit.

Optional further lemmas prove the ratio-sum≤1 bound when vertex sizes are positive, and derive that positivity from nonzero affine area and positive barycentric weights. They are not required by the parent's improved nonnegative scalar weighted argument.

`geometry-audit/` contains a byte-identical copied source and canonical pinned all-declaration audit. Its manifest is explicitly marked supporting-only and must never be counted as a separate question outcome. The module has no scalar-theorem assumption, no extra postulate, and no unfinished proof.
