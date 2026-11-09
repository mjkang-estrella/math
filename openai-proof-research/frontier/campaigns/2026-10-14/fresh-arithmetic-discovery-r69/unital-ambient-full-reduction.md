# Full-scope reduction to a unital ambient matrix product

Author supporting work for the unchanged T101G69 target, not a completed rounding theorem. Unlike high-space-completion.md this reduction allows every B<=2I and every total defect. It constructs a structured ambient algebra; it does NOT prove its operator associator small or its correction to an associative algebra.

Write R=beta²+2C, beta=||B-I||F. Fix once and for all a positive absolute threshold r_* small enough that the established r67 small-total theorem applies when R<r_*. That case is already covered by the cited author derivation. Below assume R>=r_*. Constants can depend on this fixed absolute threshold, never on dimension or T. The zero-dimensional case is vacuous.

## 1. A near-slice ambient subspace without a small-density hypothesis

Let J:V->Sym(V) send v to X_v, S=JJ*, and let S0 be the support projection of S. The nonzero eigenvalues of S are the positive eigenvalues of B=J*J. Direct index contraction gives

    ||K-S||HS²=2C,
    ||S-S0||HS²<=beta²,
    ||sqrt(S)-S0||HS²<=beta².

Here K(Y)=sum_r X_r Y X_r, acting on the whole matrix Hilbert space. The second square-root bound uses (sqrt(b)-1)²<=(b-1)² for b>=0 on positive eigenvalues. Also m-rank(S)<=beta².

Restrict K to the invariant real symmetric matrix space and let Pi be its spectral projection for eigenvalues at least1/2. This restriction is important: no skew spectral bound from exact B=I is being used. Thresholding at1/2 minimizes distance to K among orthogonal projections on that space. Comparing with S0 and using the triangle inequality gives

    ||Pi-S0||HS<=2(sqrt(2C)+beta),
    |rank(Pi)-m|<=9R,
    ||Pi-sqrt(S)||HS<=2sqrt(2C)+3beta,
    ||Pi-sqrt(S)||HS²<=18R.                           (1)

The rank inequality uses the squared distance between projections, followed by the kernel loss m-rank(S). All displayed constants are deliberately loose.

For an HS-orthonormal symmetric basis Y_a of range(Pi), let H=sum_a Y_a². As positive operators on matrix Hilbert space, Pi<=4K²: on selected eigenvectors the eigenvalue of K has modulus at least1/2, and elsewhere the left side is zero. Partial trace preserves this order. Direct contraction yields

    Tr_2(K²)=sum_rs B_rs X_r X_s <= ||B||op B <=4I.

To justify the middle order, diagonalize the positive matrix B in its coefficient indices; the sum becomes a positive weighted sum of squares of the correspondingly rotated slices. Consequently

    H<=16I.                                           (2)

No cb approximation, exact B normalization, or spectral gap beyond the threshold1/2 is needed for (1),(2).

Adjoin the physical identity matrix I to range(Pi) if necessary, orthogonally within Sym(V). Denote the resulting projection by Pi+ and its range by W, of dimension k. The added HS-unit symmetric matrix has square bounded by I. Therefore

    H_W<=17I,
    |k-m|<=9R+1,
    ||Pi+-sqrt(S)||HS²<=36R+2<=c_* R,                 (3)

where c_*=36+2/r_*. This single additional dimension is paid because R>=r_*. This step would NOT be trace-paid uniformly as R tends to zero; that is why the separate already-proved small-total case was stated first.

## 2. Frame alignment with no factor depending on dimension

Put N=max(m,k). Extend J by zero columns to an N-column matrix-valued frame. Choose an HS-orthonormal basis of W and extend its frame by zero columns to N. Orthogonal Procrustes on the coefficient spaces can align these frames X_i,Y_i so that

    sum_i ||X_i-Y_i||F²
       =tr(B)+k-2||Pi+ J||_*
       <=||sqrt(S)-Pi+||HS²<=c_* R.                   (4)

Indeed ||Pi+ J||_*=||Pi+ sqrt(S)||_* >= tr(Pi+ sqrt(S)). The latter trace is real and nonnegative. Thus expanding the last squared norm gives the claimed inequality. The SVD proof of rectangular Procrustes permits zero singular values and zero padded columns; it assumes no injectivity.

This is an orthogonal placement of the original V and W into R^N, not an identification of K(Z) with S(Z). The physical slices remain X_i, and the ambient orthonormal frame remains Y_i.

## 3. The ambient cubic is close to the original cubic

Define U_abc=tr(X_a X_b X_c). With zero padding understood, an explicit contraction gives

    U_abc-sum_t B_at T_tbc
       =sum_ij T_aij [sum_l T_bjl T_cli-sum_t T_tij T_tbc].

The bracket is a permutation, up to sign, of the original associator four-tensor. Since ||J||op<=sqrt(2), contraction and the mode Gram identity imply

    ||U-T||HS <=sqrt(2)(sqrt(2C)+beta),
    ||U-T||HS²<=4R.                                   (5)

No exact B=I identity has been substituted in (5).

On W define sigma_abc=tr(Y_a Y_b Y_c), and pad it by zero on W-perp in R^N. Cyclicity and transpose reversal make sigma fully symmetric. The frame has coefficient-to-matrix norm1 and row Gram at most17I; the original frame has coefficient-to-matrix norm at mostsqrt(2) and row Gram at most2I. For any mixed pair of these frames, the coefficient product map

    (z_ab) -> sum_ab z_ab A_a B_b

has operator norm at mostsqrt(34): group by one index, use the coefficient-to-matrix norm of the grouped family, and use the row/column Gram of the other. Pairing this product map with the difference frame in (4), and telescoping the three factors, proves

    ||sigma-U||HS <=3sqrt(34)||Y-X||HS.

Hence

    ||sigma-T||HS² <=(8+612c_*)R.                      (6)

The vectors indexing the two tensors in (6) use their aligned embeddings into R^N.

Moreover B_sigma<=17I: for every Y in W,

    sum_b ||Pi+(Y Y_b)||F² <=sum_b ||Y Y_b||F²
       =tr(Y² H_W)<=17||Y||F².

Finally W contains I. Under the matrix-to-coefficient isometry, the vector corresponding to I is an EXACT unit for the projected product Pi+(YZ), since Pi+(IY)=Y. The unit has norm sqrt(m); no dimension-independent bound on its norm is asserted or used.

## 4. Defects and transfer of a future correction

The strong Gram and associator defects of sigma are O(R). Here is a direct way to check this without inferring operator-smallness. For symmetric tensors F,G whose flattening Grams are bounded by a fixed constant, the Gram identity J_F*J_F-J_G*J_G gives

    ||B_F-B_G||F <= (||J_F||op+||J_G||op)||F-G||HS.

For either pairing of the associator, expand its difference as a contraction with one changed tensor. The other contraction has operator norm at most the corresponding flattening norm. The two pairings therefore give

    ||A_F-A_G||HS <=2(||J_F||op+||J_G||op)||F-G||HS.

Apply these to the padded tensors in (6), whose Gram bounds are2 and17. Padding T contributes N-m<=9R+1 to its squared Gram defect, and no associator defect. Consequently

    ||B_sigma-I_W||F²+||A_sigma||HS² <= absolute_constant*R.

This is a total Hilbert--Schmidt estimate. It does not bound any associator operator flattening by a small constant.

If the resulting unital ambient cubic could be rounded to unit orthodeco in W at squared cost O(R), the original full target would follow. Extend that orthodeco tensor to R^N by unit axes on W-perp. The extra cost against the zero-padded sigma is N-k<=9R+1. Compress to the original V, and use the established frame-compression estimate, costing at most16(N-m) in squared distance. Together with (6), every cost is O(R). This handles both k<m and k>m and does not assume an injective physical-to-ambient projection.

## 5. Remaining complete-algebra obligation

The new full-scope reduction produces an EXACTLY UNITAL, fully symmetric compressed matrix product on dimension at most m+O(R), with an HS-orthonormal matrix representation, bounded row Gram, and total defects O(R). It explicitly retains latent matrix modes.

It does not produce an associative algebra, a small operator associator, or a bound on the norm of the unit independent of dimension. The required next theorem is a trace-paid correction of these structured unital compressed products, allowing O(R) exceptional modes without cascading loss. Applying the small-operator correction from r69 to sigma without proving its hypotheses would be invalid.

All ingredients here are direct author calculations, classical spectral truncation and Procrustes, plus the previously proved small-total and frame-compression support. No external quantitative algebra theorem, independent gate, novelty verdict, or replacement nominee is claimed. The full frozen all-dimensional, all-error target remains unchanged and open.
