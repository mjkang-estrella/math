# I206: independent contribution assessment of the odd-prime socle family

2026-10-12. **TECHNICAL/KNOWN ONLY.** This is a contribution assessment, not a completed independent proof gate. Both final acceptance decisions remain with the parent. The eight accepted findings and all source results/lower operations at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are unchanged.

The family supplies real information about the actual quotient multiplication. Nevertheless, its proof adds a short, standard deduction to established invariant-theoretic and Alon–Tarsi inputs. Its first case is explicitly known. The bounded reading did not locate the all-prime socle formulation or its full displayed polynomial identity verbatim; that is not evidence of worldwide novelty. The verdict does **not** assert that a publication containing the exact all-prime sentence has been found.

## 1. Statement being assessed

Over the complex numbers, use the natural multiplication on

    R = direct_sum_j Sym^p(Sym^j V),
    A = C[R_1] contained in R,       C = R/A as a graded A-module.

For each odd prime p the claim is that the unique copy

    W_p = S_((p-1)^p) V contained in R_(p-1)

maps injectively into C_(p-1), is annihilated by A_1, and hence by A_+. It is nonzero for dim V >= p and zero for dim V < p. This formulation keeps the quotient as a module: A is a subalgebra, not an ideal of R.

The algebra conventions and the identification A_j = im(mu_(p,j)) are in the accepted sixth-power reduction, `eq:multmap`. No new proof of the accepted source results is attempted here.

## 2. Exact literature overlap

**Kumar–Landsberg.** [Proposition 2.1](https://people.tamu.edu/~jml/KLfoulkeshowefinal.pdf) constructs the multiplicity-one rectangular invariant of degree d on degree-r forms in d variables for even r, by symmetrized determinant contractions. Its proof checks symmetry, invariance and nonzero evaluation. Their Theorem 1.9 concerns the even-order square Alon–Tarsi problem, not the odd-prime socle statement. The construction, however, applies with d=p and r=p-1, and is enough to recover the covariant used here by the explicit substitution below. Calling the entire method a new odd-order contraction would miss this overlap.

**Kotlar and Drisko.** [Kotlar, Theorem 2.2](https://arxiv.org/abs/1204.5276v2) gives exactly the scalar used in I202:

    [product_(i,j) X_ij] per(X) det(X)^(n-1)
      = (-1)^(n(n-1)/2) n!(n-1)! AT(n)       (n odd).

The definition is the signed count of normalized unipotent squares. Kotlar's Corollary 3.6 and [Drisko, Theorem 4](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v5i1r28/pdf/) give AT(p) = (-1)^((p-1)/2) modulo p. Both proofs were read. These are established nonvanishing inputs, not new prime-order counting results. Kotlar's different identity in Proposition 4.1 uses the reduced-square imbalance; it is not a license to substitute that imbalance for AT(n).

**Chow normalization and an exact known case.** [Raicu–Sam–Weyman, Theorem 2.3 and the sequence after Remark 2.9](https://arxiv.org/abs/2108.10910v1) give the normalization and the same deficiency module, with different letters: their B is our R, their k[Y] is our A, and their C is our C. Most decisively, Corollary 4.6(a) identifies C_(3,2) with det(U)^2 concentrated in degree 2. Consequently its positive-degree action is zero. Example 4.5 exhibits the Hessian/linear-coefficient relation realizing that action. This is the claimed p=3 case in dimension three, indeed a description of the entire quotient there. Extension of this constituent's annihilation to larger dimensions uses the same formal length argument as I202.

There is also a known p=5 consequence. Kumar–Landsberg Proposition 1.8 records the complete kernel of the diagonal map h_(5,5), crediting an unpublished Ikenmeyer–Mkrtchyan calculation. The partition (9,4,4,4,4) is absent. Since this map is an endomorphism of one semisimple representation, that type is absent from its cokernel too. Combined with the length obstruction in degree four and Pieri, this already implies A_1 W_5=0. This is an inference from their stated kernel result, not a computational verification performed here.

**Further representation-theoretic comparison.** [Kumar, Sections 2–6](https://arxiv.org/abs/1109.5996v2) supplies the rectangular invariant construction, the translation from nonzero evaluation to actual coordinate-ring occurrence, and the Latin-rectangle/isotypic-component comparison. Its principal results are for even form degree and rectangular weights. They do not state annihilation of this odd-degree quotient constituent. In particular the partition of the multiplication image here, (2p-1,(p-1)^(p-1)), is not the rectangular conclusion of those theorems. The ordinary Foulkes comparison and actual canonical image must remain distinct.

The all-prime socle theorem and its precise full identity were not located as stated in these papers. No claim is made about unread papers cited by them. The literature record gives the complete reading boundaries and the limited search coverage.

## 3. What the proof adds, and why the bridge is routine

Here is an explicit comparison, rather than a judgment based on the number of familiar ingredients. Put n=p for the application and define, in n variables,

    Omega = det(partial / partial x_(j,k)),
    I_(n-1)(G) = [Omega^(n-1) product_(j=1)^n G(x_j)]_(all x_j=0).

For G of degree n-1, I_(n-1) is precisely a differential normalization of the rectangular determinant-contraction invariant of Kumar–Landsberg Proposition 2.1, with their d=n and their even degree r=n-1. For a degree-n form F let D_y F(x) = sum_k y_k partial_k F(x). Direct commutation of the constant-coefficient operators gives

    I_(n-1)(D_y F)
      = [Omega^(n-1) product_(j=1)^n F(x_j)]_(all x_j=y)
      = K(F;y).

Indeed, after Omega^(n-1), every block x_j has degree one. Applying D_y in that block and setting x_j=0 equals evaluating its remaining linear polynomial at y. This equality holds for every F. Thus the covariant is the known invariant applied to a directional derivative; no new invariant construction is needed. This identification is a deduction in this review, not a quotation falsely attributed to the paper.

The rest of the passage to actual multiplication is also explicit. On F_0(y)=y_1...y_n, the uncontracted cells form a permutation matrix, so K(F_0;y)=kappa_n F_0(y), with kappa_n exactly Kotlar's coefficient. For F_L(y)=product_i(sum_k L_ik y_k), the chain rule gives

    K(F_L;y) = kappa_n det(L)^(n-1) F_L(y).

It holds on invertible matrices and therefore on every L by polynomial identity. Coefficients of K are degree n in the coefficients of F. When kappa_n is nonzero, coefficient comparison puts det(L)^(n-1) times every generator of A_1 in A_n. This is the necessary actual-image step; merely observing a Schur constituent would not establish it. Here the step is paid by a direct covariant substitution and coefficient comparison, not by solving another plethysm rank problem.

Finally, the Cauchy label factor of the rectangle is det^(n-1), of dimension one; its row permutation action is trivial because n-1 is even. The source in degree n-1 has length at most n-1, so the n-row rectangle survives. Pieri gives only one summand of W_n tensor Sym^n V with at most n rows, namely S_(2n-1,(n-1)^(n-1)) V. All others have n+1 rows and vanish in the multiplication target. Evaluation in dimension n detects the remaining natural multiplicity map, and generation of A by A_1 gives the socle assertion.

These formal steps do add a useful quotient interpretation to the cited formulas. They do not supply a substantive new bridge beyond determinant contraction, the known AT scalar, chain rule/polynomiality, Schur length and Pieri. The same reasoning works for each odd n >= 3 with AT(n) nonzero; primality enters only through the old nonvanishing theorem. This extension is not itself a new nonvanishing result for composite n. No converse equating socle membership with AT(n) nonvanishing is established.

## 4. Demonstrated consequence and significance boundary

The strongest demonstrated contribution is an explicit infinite family of irreducible submodules of the socle of the Chow normalization deficiency module, together with polynomial representatives for their degree-one products in A. This is stronger than just showing that W_p occurs in R_(p-1) or in C_(p-1).

There is a recognized mathematical setting: the paragraph after Remark 2.9 of Raicu–Sam–Weyman asks for further study of C and of the least stabilization degree; Problem 3.3 asks for resolutions of their modules of covariants. The present family gives limited structural data in that setting. It neither determines C nor its resolution or least stabilization degree. It cannot inherit the full significance of those open-ended problems merely by furnishing one constituent family. No new consequence for Rota's basis conjecture, a GCT obstruction, or the general Foulkes comparison is demonstrated by this argument.

At p=7 it proves A_1 W_7=0 and hence A_1^2 W_7=0. The accepted module-generation operation identifies the full target with A_1^2 C_6=0. The class D^2 z(e_1)^4 of weight (30,2,2,2,2,2,2), already displayed in I202, survives in C_6 by the same length obstruction and is outside W_7. The missing assertion remains

    A_1^2(C_6/W_7)=0.

There is no control here of that remainder's products. Thus this result does not establish a new canonical surjectivity range or the ordinary seventh case. The p=3 case supplies no novelty: the literature already determines the whole quotient in that dimension. The combination of exact known base case, routine general bridge and limited demonstrated consequence supports retention as technical progress rather than nomination as a substantial new finding.

## 5. Mathematical cautions and review status

No flaw requiring a correction of the stated odd-prime theorem was identified in this contribution-focused reading. The claims rely on characteristic zero; kappa_p itself is divisible by p, so the modular argument must concern AT(p), before multiplication by factorials. Determinant parity, extension over singular L and the all-dimension Pieri step cannot be omitted. These are handled in the supplied argument. The quotient has an A-action, not an R-algebra product, and this is not a full conductor calculation.

The exact broader sufficient statement is: for any odd integer n >= 3 with the normalized-unipotent constant AT(n) nonzero, over C the multiplicity-one S_((n-1)^n)V in R_(n-1) embeds in C_(n-1) and is annihilated by A_+; it is nonzero exactly when dim V >= n. This restates I202's already explicit extension, without altering its files. No wider characteristic assertion is justified here.

This review checked the deduction enough to assess its contribution and to identify source overlap; it is not the separately commissioned independent proof-acceptance review. No source theorem was audited against the accepted baseline, and no numerical computation, research code, test, replay, snapshot, seal, subordinate agent, staging, commit or publication was performed. Only this review, its authentication JSON, its literature record and four fully read source-copy files were written. Partial notes preceded the final verdict.
