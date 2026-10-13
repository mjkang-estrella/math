# I202: the actual Foulkes deficiency module

2026-10-12. **UNRESOLVED — NO SUBSTANTIAL NOMINATION.** Eight findings remain accepted; two remain. All corpus theorems and lower operations at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are accepted. Both independent acceptance gates remain with the parent.

## Exact target and paid progress

The target remains surjectivity, for every finite-dimensional complex V, of

    mu_(7,8): Sym^8(Sym^7 V) -> Sym^7(Sym^8 V).

It is enough to work in dimension seven. In the source normalization algebra, with C=R/A regarded as an A-module, the target is exactly A_1^2 C_6=0. Neither this target nor the ordinary seventh Foulkes case is proved or refuted here.

There is new concrete progress on the actual multiplication: **the determinant class (det V)^6 in C_6 is annihilated by A_1 already**, so its second products vanish as well. This resolves the particular membership question left open in I199, not the whole deficiency module.

More generally, for every odd prime p and every finite-dimensional complex V, the rectangular submodule S_((p-1)^p)V survives in C_(p-1) for a=p and is annihilated by A_1. It is nonzero when dim V>=p and is a socle submodule. The [analytic record](../experiments/i202_foulkes_quotient/analytic-attempt.md), §2.1, gives the exact statement and full proof, including extension from dimension p to arbitrary dimension.

The proof constructs the polynomial covariant

    K(F;y) = [det(partial/partial x_(j,k))^(p-1)
                product_(j=1)^p F(x_j)]_(all x_j=y).

For F=product of the p linear forms with coefficient matrix L, it proves

    K(F;y)=kappa_p det(L)^(p-1) F(y).

Here kappa_p is the squarefree coefficient in per(X)det(X)^(p-1). [Kotlar, Theorem 2.2 and Corollary 3.6](https://arxiv.org/abs/1204.5276) give its exact signed value and nonvanishing for odd primes via AT(p). Coefficients of K are degree-p polynomials in coefficients of F; this proves actual image membership. The proof does not infer it from ordinary plethysm occurrence or nonzero multiplication in R, and does not assume positivity of a Latin-square count.

The remaining module is genuinely larger. For example D^2 z(e_1)^4 is a nonzero highest vector of type (30,2,2,2,2,2,2) in R_6 and survives in C_6 by the six-row bound on A_6. It is distinct from (6^7). No claim is made that its products survive in C_8. After removing the proved socle submodule W_7, the still-missing estimate is

    A_1^2 (C_6/W_7)=0.

## Two routes and their precise stopping points

**Route I: actual multiplication and invariant relations.** After separate homogenization, C_j is identified with B_[j]/E_[j], where B_[j] consists of seven-row multisymmetric polynomials of degree at most j in each row, and E_[j] is the span of products of at most j polarized elementary generators. The target is the filtered straightening estimate

    E_[2] B_[6] is contained in E_[8].

Domokos's complete trace-relation presentation, read in its primary source, was applied to this problem. It bounds the number of polarized power sums, not elementary-generator length. These lengths differ drastically: a single trace p_(y^42) requires elementary length 42. Such terms occur and cancel even in the trace expansion of product_i y_i^6=e_7(y)^6. No straightening preserving the needed row-degree cancellation and elementary length eight was found. The exact presentation does not itself imply the missing filtered estimate.

**Route II: complete all-slot jets.** The record derives the coefficient identities with repeated factor indices, extending the previously retained squarefree identities. It also differentiates the compatible gradient vanishing to obtain full tangent-Hessian constraints at x^6 yz. These constraints are necessary but insufficient: an explicit binary degree-seven polynomial q(P)^2 a_0(P)^3 satisfies all those singularity constraints and is nonzero at the split product X^8+Y^8. It is therefore excluded by the original product condition.

Keeping the complete identities gives an exact pair of row/column symmetrizers on 56 tensor positions. The remaining assertion is injectivity of column averaging on the row-symmetric subspace, or strict positivity of P_H P_K P_H there. Orthogonal projections prove nonnegativity only. The known diagonal canonical kernels rule out a general positivity argument of that kind. Neither a (7,8)-specific strict estimate nor a compatible nonzero kernel vector was obtained.

## Contribution and delivery boundary

The odd-prime socle family is a proved auxiliary result in this attempt. It is not certified new to the literature or substantial enough for nomination: determinant contractions and their Latin-square relationship are established in Kumar–Landsberg, and the nonvanishing input is Kotlar's known theorem. The [literature record](../sources/i202_foulkes_quotient/literature.md) states the primary-source boundaries explicitly. No novelty claim follows from unsuccessful searches.

The [analytic record](../experiments/i202_foulkes_quotient/analytic-attempt.md) includes proofs and counterexample checks. The [reading and failure log](../experiments/i202_foulkes_quotient/reading-and-failures.md) records the failed estimates, and the [authentication record](../experiments/i202_foulkes_quotient/input-authentication.json) binds only actual read inputs, with their precise scopes. Partial records were preserved during the attempt.

Only the authorized I202 files and fully read source copies were written. No agents, research code, numerical scans, tests, certificate replay, snapshots, seals, staging, commits, or publication were used. No I31, shared, ancestor, or other live-task files were edited.
