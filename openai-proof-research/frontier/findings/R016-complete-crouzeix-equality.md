# R016 — Complete polynomial equality is scalar in dimension four

**Accepted as the tenth substantial finding.** The [I242 argument](../experiments/i242_crouzeix_four_dimensional_rigidity/analytic-attempt.md) passes the [independent I245 proof gate](../reviews/i245-crouzeix-rigidity-proof.md) without repairs. The [independent I246 contribution gate](../reviews/i246-crouzeix-rigidity-contribution.md) classifies its complete-witness scalarization as substantial. The parent read both full reviews, checked the central calculations and verified their final artifacts and source records. This is a written mathematical validation, not a formal proof certificate or a claim of worldwide priority.

## Exact theorem

Let 1<=n<=4, let A be a complex n by n matrix, and let P(z)=sum_k z^k C_k be an m by m matrix-valued polynomial, for any finite m>=1 and any finite degree. Use the Euclidean operator norm and the base-first evaluation

    P[A]=sum_k A^k tensor C_k.

Let W(A)={x*Ax: ||x||=1} and M=max_{z in W(A)}||P(z)||. If M>0 and

    ||P[A]||=2M,

then W(A) is a nondegenerate closed disk. More strongly, there are constant unit vectors u,v in C^m such that the scalar polynomial

    p(z)=v*P(z)u

satisfies

    ||p(A)||=2M,      max_{z in W(A)}|p(z)|=M.

If W(A)=a+rho Dbar, rho>0, then

    p(a+rho z)=M eta z^k

for some |eta|=1 and integer 1<=k<=deg P. Thus each nondisk A of size at most four has strict inequality for every individual nonzero polynomial witness. This does **not** assert a uniform gap below two when the polynomial varies.

The scalar-witness conclusion and disk conclusion constitute **one finding**. No inverse-polynomial condition, simple-spectrum assumption, regularity of the numerical-range boundary, or fixed coefficient-size bound is imposed.

## Dependencies and the actual increment

The complete factor-two inequality is a premise, not this finding. The stipulated corpus is OpenAI/math at revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb:

- [Direct complete Crouzeix proof](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-direct-proof-of-the-complete-Crouzeix-inequality-September-26-2026): the complete bound, analytic outer approximation, Faber coefficient inequalities, original-matrix positive resolvent and both ordered multiplication tests.
- [Structural companion](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-complete-Crouzeix-theorem-September-23-2026): conventions and the distinction between the original positive field and the similar matrix's normalized density.

The external scalar input is [Jin, *Rigidity at the Extremal Crouzeix Constant*, v2](https://www.preprints.org/manuscript/202609.0079/v2), Theorem 1 and Lemma 4. Its all-dimensional scalar disk theorem and finite scalar Schur interpolation uniqueness are credited inputs. They are applied only after constructing a scalar witness.

The closest comparison, [Åhag–Czyż–Virtanen v3](https://arxiv.org/html/2608.27346v3), Sections 5, 7 and 11, already supplies finite rectangular compression, Schmidt orthogonality, scalar classification and complete rigidity through base dimension three. Its dimension count leaves a two-sided coefficient configuration in dimension four. The new step converts the complete positive-block equality into a geometric rank constraint, forcing one-dimensional coefficient input and output for the specified P.

## Proof

Normalize M=1. Decompose A into unitarily irreducible reducing blocks and choose B with ||P[B]||=2. The stipulated bound gives max_{W(B)}||P||=1. Its size d is between two and four. A boundary eigenvector of B would also be an adjoint eigenvector, by positivity of a supporting Hermitian slack, contradicting irreducibility. Thus sigma(B) lies strictly inside K=W(B), and K has interior.

Choose a fixed unit maximal singular pair x=vec(X), y=vec(Y) for P[B]. Let Omega_j be analytic convex outer neighborhoods shrinking to K, with normalized exterior maps h_j(z)=c_j z+c_{0,j}+O(z^-1). Choose r,R>0 with r Dbar subset K subset Omega_j subset R Dbar after translation. Schwarz's lemma bounds r<=c_j<=R.

Convexity gives Re(1+z h_j''/h_j')>=0. The exterior Herglotz formula therefore yields probability measures mu_j with

    log(h_j'(z)/c_j)=2 integral log(1-xi/z) dmu_j(xi),
    |h_j'(z)|<=4c_j.

Their logarithmic Fourier coefficients have uniformly square-summable tails, bounded by 4 sum_{k>N} k^-2. Weak convergence of mu_j consequently gives strong boundary L2 convergence of the logarithms. Since exponentiation is 4-Lipschitz on Re z<=log 4, h_j' and q_j=z h_j' also converge strongly in L2. Equi-Lipschitz boundary maps and exterior inverse normal families identify the limit h as the exterior map of K. On a regular analytic arc, reflection identifies its nonzero derivative and outward normal.

The fixed interior spectrum bounds (h_j I-B)^-1 uniformly. Hence

    R_j=q_j(h_j I-B)^-1,       H_j=R_j+R_j*

converge strongly in L2 to the original positive boundary field R and H. In particular the Faber coefficient energy a_j^2=||Y*R_j X||_L2(HS)^2 stays bounded. This is the necessary control before passing equality from a strict enclosing domain to K.

Let M_j=max_{Omega_j}||P|| and gamma_j=2/M_j -> 2. The direct source's exact residual identity is

    E_X,j+E_Y,j+E_B,j+2 T_j
      =2(4/gamma_j^2-1)a_j^2,

where all terms are nonnegative and

    T_j=3||Y*X||_HS^2+sum_{k>=1}||X*b_{k,j}(B)Y||_HS^2.

It follows that X*Y=0 and E_B,j ->0. Put D=XX*-YY*. The positive-block slack has the pointwise form

    tr(H_j D H_j D)=||H_j^(1/2) D H_j^(1/2)||_HS^2.

Strong L2 convergence passes this quadratic trace in L1. Thus H^(1/2) D H^(1/2)=0 almost everywhere: ran H is totally isotropic for D. If p=rank X and q=rank Y, orthogonality gives inertia (p,q,d-p-q), so every such subspace has dimension at most d-max(p,q).

There is an open regular boundary arc with a simple maximal support eigenvalue. To see this, suppose no direction had a simple top eigenvalue of Re(e^-i theta B). Opposite directions also make every bottom eigenvalue multiple. For d<=3 the pencil would be scalar. For d=4, after centering, every pencil value has eigenvalues +s,+s,-s,-s and squares to a scalar. Its Hermitian generators satisfy

    H_0^2=alpha I, K_0^2=beta I,
    H_0 K_0+K_0 H_0=2c I.

Subtracting the H_0 component from K_0 gives anticommuting Hermitian generators. Elementary block diagonalization makes them two identical two-dimensional pairs, or a commuting degenerate pair. Both contradict irreducibility. Thus a simple top direction exists. Its curvature radius is

    lambda+lambda''
      =2 sum_{j!=top} |v_j*H_theta' v|^2/(lambda-lambda_j)>0;

vanishing would give a common eigenvector of B and B*. This produces the required regular analytic arc.

On that arc the resolvent congruence makes rank H=d-1. Its circle preimage has positive measure, so the almost-everywhere isotropy identity applies there. Therefore d-1<=d-max(p,q), forcing p=q=1.

In the base-first convention write X=xi u^T and Y=eta v^T, with all factors unit. Then x=xi tensor u, y=eta tensor v, and

    eta* (v*P u)(B) xi = y*P[B]x=2.

Thus p(z)=v*P(z)u is a scalar equality witness, bounded by one on the **full** W(A), not only W(B).

Jin's scalar rigidity gives W(B)=a+rho Dbar. For T=(B-aI)/rho and g(z)=p(a+rho z), the spectral jets determining g(T) have minimum Schur interpolation norm one. Indeed, an interpolant of norm c<1, radially dilated and approximated by polynomials, would imply ||g(T)||<=2c<2 using the stipulated bound. Jin's finite interpolation uniqueness therefore makes g a finite Blaschke product. Since it is a polynomial, g(z)=eta z^k with k>=1. Its bound on W(A) forces W(A) inside a+rho Dbar, while W(B) supplies the reverse inclusion. Restoring M proves the theorem.

The [full I245 check](../experiments/i245_crouzeix_rigidity_proof/analytic-check.md) supplies the detailed limit orders, inverse-map argument, tensor conventions and interpolation justification.

## Validation and limits

- **Proof:** I245 PASS, no repairs, on exact candidate hash 03c0f05cef564e1bde2630ed725ff755d3bb603ea07dbd39a711e595e96d6627.
- **Contribution:** I246 SUBSTANTIAL, for the complete input-witness scalarization and its dimension-four consequence, not merely for changing three to four.
- **Counterexample pressure:** the known matrix-valued witness producing the weighted chain (1,2,1) still refutes scalar output nilpotent rigidity. It is consistent with this theorem because a scalar input compression p(z)=z exists. Disk-contained reducing summands prevent any claim that all of A is a single nilpotent block.
- **Provenance:** final review artifacts, recorded source hashes and pinned blob identities were checked; exact read extents remain in the two reviews' source indexes.
- **Scope:** no positive-deficit power law, uniform strict gap, higher-dimensional classification, rational/holomorphic witness extension, or nonattained complete-supremum claim is accepted. The broader independently developed [I243 candidate](../iterations/i243-scalarization-parent-disposition.md) remains outside this finding's reviewed scope.
- **Priority:** the primary comparison supports substantiality within the inspected literature; worldwide novelty and external peer review are not certified.

Candidate commit: ad8969f1. Independent proof integration: dd9c31cc. Independent contribution integration: aa2929a0. This acceptance has its own commit.

**Ten accepted substantial findings; the requested target is complete.**
