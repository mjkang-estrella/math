# A diagonal maximum for every geometric Vandermonde inverse

**Research status: candidate new resolution; no discovery count authorized.**
The mathematical argument and Lean theorem resolve the complete source conjecture at every positive order, including its stated index bound. Strict novelty acceptance still requires independent adversarial mathematical and prior-art review.

## Exact target and conventions

MathDB 347481, UUID `5942f855-53c1-4349-b415-4f49e2e3a9a3`, has no solutions, comments, replies, or model attempts in the live API snapshot. Source: Carlo Sanna, Jeffrey Shallit and Shun Zhang, *The Largest Entry in the Inverse of a Vandermonde Matrix*, arXiv:2008.01012v1 (3 August 2020), Conjecture 11. The accepted manuscript dated 11 December 2020 (published in *Linear and Multilinear Algebra* 70(20) (2022), 5634–5641, DOI 10.1080/03081087.2021.1922337) retains the conjecture as Conjecture 12.

For real b>1 and integer n>0, let V=(b^(ij)) indexed by 0≤i,j<n, and C=V^(-1). Set M_b(n)=max_{i,j}|C_ij| and n0=ceil(log_b(1+1/b)). The conjecture asks that, for all sufficiently large n, M_b(n)=|C_ii| for some i≤n0. The row convention is V(a)_ij=a_i^j. For geometric nodes a_i=b^i this is exactly the symmetric matrix above, so transpose conventions cannot change the claim.

## Stronger conclusion

For every n>0, there exists 0≤i<min(n,n0+1) such that M_b(n)=C_ii>0. Thus the eventual quantifier can be replaced by every positive order. This constitutes one proposed resolution, not a collection indexed by n or b.

## Proof of diagonal maximality

The matrix V is symmetric. For each 1≤r≤n its leading principal determinant is

    det V_r = product_{0≤i<j<r}(b^j-b^i)>0.

Sylvester's criterion therefore shows that V is positive definite. Consequently C=V^(-1) is positive definite. Cauchy–Schwarz for the inner product x^T C y gives

    |C_ij|² ≤ C_ii C_jj.

Choose i maximizing the positive diagonal entries. Then every |C_jk|≤C_ii. This proves diagonal maximality at every order.

The Lean proof uses a second proof of positivity to avoid assuming an unformalized Sylvester criterion. For c=log b>0 and x_i=i,

    b^(ij) = exp(c i j) = sum_{k≥0} (c^k/k!) i^k j^k.

Each summand is a nonnegative multiple of a rank-one positive semidefinite matrix. The cone is closed, hence V is positive semidefinite. Its ordinary Vandermonde determinant is nonzero, hence it is positive definite. The remaining steps are exactly the argument above.

## Proof of the source's index bound

If n≤n0+1 there is nothing further to show. Suppose n≥n0+2. Put

    pi_j = product_{0≤h<n,h≠j}|b^j-b^h|,
    sigma_{r,j} = sum_{S subset {0,...,n-1}\{j}, |S|=r} b^(sum S).

Lagrange interpolation gives |C_ij|=sigma_{n-1-i,j}/pi_j. Replacing an excluded node j by j+1 replaces the possible node b^(j+1) by the smaller b^j in the numerator, so sigma_{r,j+1}≤sigma_{r,j}. Direct cancellation gives

    pi_(j+1)/pi_j = (b^(n+j-1)-b^(n-2))/(b^(n-1)-b^j).

For j≥n0, b^j≥1+1/b. Since

    (b^(n-1)+b^(n-2))/(b^(n-1)+1) < 1+1/b,

that ratio is at least one. Therefore |C_i,j+1|≤|C_ij| for every i and j≥n0. Symmetry gives the corresponding row monotonicity. In particular C_jj≤C_n0,n0 for every j≥n0. Combined with the already proved diagonal maximum, this places a global maximum at an index i≤n0.

These are precisely the verified ingredients of source Theorem 1; the new missing observation is positive definiteness and its diagonal consequence. The complete claim uses the proved source theorem, not an extra conjecture.

## Scope and credit

The matrix definition, determinant formula, localization ingredients and original conjecture are due to Sanna–Shallit–Zhang; positive-definite matrix theory is classical. Proposed new contribution: the observation that this specific geometric Vandermonde matrix is positive definite, resolving their still-stated conjecture uniformly in n. This is not a new general theorem about positive definite matrices, a typo correction, a numerical conjecture, or a claim of absolute worldwide priority.

A serious prior-art screen is recorded in NOVELTY.md. The full Lean endpoint `source_conjecture_all_orders` now includes the index bound. Independent adversarial review remains required before strict tally acceptance.

## Certificate inventory and interpretation

`formal/VandermondeDiagonal.lean` is one self-contained module. Main theorem `source_conjecture_all_orders` states that for every real b>1 and positive n, there exists i:Fin n with i.val≤ceil(log_b(1+1/b)) such that every inverse entry has absolute value at most the absolute diagonal entry at i. Since that diagonal entry is itself included among the entries, this is exactly equality to the global maximum M_b(n). It proves the source's eventual claim with the stronger threshold n=1. The cutoff is the natural-number ceiling; its real argument is positive for b>1, so it coincides with the source's integer ceiling. All matrix conventions and positive-order hypotheses are preserved.

The formal localization proves the Lagrange inverse coefficient bridge, the exact absolute-coefficient formula, numerator monotonicity, two exact denominator recurrences, denominator monotonicity beyond the cutoff, and the final finite-index extraction. No proved external source theorem remains as an unproved Lean assumption.
