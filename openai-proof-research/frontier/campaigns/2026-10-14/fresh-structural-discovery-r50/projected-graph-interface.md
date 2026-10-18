# One omitted inverse coordinate: author derivation

This is a candidate repair, not an independently reviewed theorem. Let B be an invertible symmetric bit matrix, C=B^{-1}, a one fixed coordinate, and P the coordinate deletion map omitting a. Consider columns z with zᵀCz integral (specifically0 or1) and ||PCz||≤L sqrt(N), without a bound on (Cz)_a. The source's full graph norm bound need not apply.

Partition this set by z_a∈{0,1}, then use the source pairing colors and robust extraction. Differences x lie in E={x_a=0}. Define γ'(x)=(x,PCx). This map is rational and injective, and its image differences have norm at most sqrt(1+4L²)sqrt(N). The source robust-image lattice determinant bound therefore applies unchanged. First-coordinate projection still sends every radical lattice injectively to an integer lattice, so its covolume is at least1. The finite discriminant pairing on differences remains exactly xᵀCy modulo Z; omitting a coordinate of the graph does not change that pairing or its image order.

On Γ'=γ'(E) put q(γ'x,γ'y)=xᵀCy. Because x_a=y_a=0, q=xᵀPᵀPCy. Thus |q(γ'x,γ'x)|≤||x||||PCx||≤(1/2)||γ'x||². All eigenvalues of q in the projected graph metric have absolute value at most1/2; a large omitted inverse coordinate cannot create an uncontrolled operator norm.

Suppose B has at most ξN eigenvalues in [-w sqrt(N),w sqrt(N)]. Let V be the span of the remaining eigenvectors. On

    E ∩ V ∩ {x:(Cx)_a=0}

the projected graph metric equals the full graph metric and |q|≤(w sqrt(N))^{-1} times that metric. This subspace has codimension at most ξN+1 inside E. The min–max principle, separately for positive and negative eigenvalues, bounds the number of singular values of q exceeding (w sqrt(N))^{-1} by2ξN+2. This is a restriction of quadratic forms, not an assertion that C commutes with the coordinate projection.

For a robust difference span F⊂E of low height, the source simultaneous inverse-form rank bound still gives rank(q|γ'F)≥dim F−ξN. Its pairing determinant lower bound is N^{-NJ_B} exp(-O_L(N log log N)). Its upper bound is at most (1/(w sqrt(N)))^{(rank(q|γ'F)−2ξN−2)_+}, since all other singular values are at most1. Therefore the same comparison gives

    dim F / N ≤ 2J_B + 3ξ + o(1).

The additional bit partition loses only a factor2. Shrinking ξ and the source W2 threshold should give a subexponential column count with one omitted inverse coordinate. The source height-two-layer argument uses only integrality of the quadratic value and cube membership, hence does not require a full inverse norm in its other case.

Remaining checks: exact finite-pairing color statement and graph-image hypotheses; complete primary operation comparison; fair-p endpoint of the biased lower argument; corank reduction across subexponentially many fixed-diagonal patterns; source path construction with conditional fixed diagonals; all steps of the tail normalization and typical-row selection. A proof of this interface alone would not be counted as a separate substantial result.

## Subsequent simplification before sealing

The preceding codimension argument is valid but unnecessarily weak. On E the projected graph is exactly the ordinary graph of the symmetric principal compression C_E=C[j^c,j^c], and q is its defining form. Thus the graph eigenvalues are λ(C_E)/(1+λ(C_E)^2). Interlacing gives at most ξN large absolute eigenvalues of C_E when C has at most ξN, so the source bound is2J_B+2ξ+o(1). candidate.md uses this simpler proof. This substantially reduces the case for a nonroutine contribution: the repair is the source graph construction applied after one bit-fiber restriction and principal compression. The stronger outcome alone is not a substantiality argument.

Affine-domain precision: when the chosen fiber has z_j=1, its points are not in E. Apply the global map Φ(x)=(x,P_j Cx) to the affine span and use γ'(v-v')=Φ(v)-Φ(v') on differences. The candidate uses this notation. Parent author checks requested this clarification and the sign-to-bit small-interval threshold adjustment; neither is an independent gate.
