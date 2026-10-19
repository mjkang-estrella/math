# A compatible matrix-splitting reduction, before any freeze

This is a feasibility/comparison calculation, not a frozen candidate. Its complete scope is finite families of positive semidefinite matrices on any finite-dimensional real or complex Hilbert space, with no commutativity, spectral gap, bounded condition number, large-parameter or subsequence restriction. Constants 10 and 20 below are absolute. It does not preserve the sum of the approximants.

## Paid source and primary contracts

Pinned source126, `splitting.tex`, proves an orthogonal splitting with off-label squared Frobenius error at most `2^(m−1) O`, where `O=sum_(i≠j) tr(A_i A_j)` and there are m labels. Its proof uses the positive/negative spectral spaces of a two-matrix difference, then induction and overlap accounting. The `matching.tex` proof uses this within smoothing and a low-degree signed pseudomoment argument. Its exact main theorem already covers every fixed shift 0<rho<1 with an exponential-rate constant independent of rho; rho=1 is explicitly a different, small diagonal factorization endpoint. The uniform matching-smoothing theorem already includes every admissible fixed-cell edge-count table, including rare and unbalanced tables. Changing those parameters is not the present operation.

Mikael de la Salle, *Orthogonalization of positive operator valued measures*, C. R. Math. 360 (2022), 549–560, [published primary PDF](https://comptes-rendus.academie-sciences.fr/mathematique/item/10.5802/crmath.326.pdf), Theorem 2: for a POVM a_i and a normal state phi, a defect less than epsilon in `phi(sum a_i²)` yields a PVM P_i with `phi(sum |a_i−P_i|²)<9 epsilon`. The state need not be tracial. The finite-algebra proof in §3, including Lemmas 6 and 7, was read. In fixed finite dimension compactness of the set of PVMs gives the non-strict version with defect delta by epsilon decreasing to delta. For delta=0, the same limit applies.

For real matrices this is the same finite proof over real spaces, not an average of complex projections: the extremization in Lemma 6 occurs in real symmetric operators commuting with the relevant a_i; two fractional eigenvectors admit the same real rank-one perturbation preserving the total trace. Extreme effects therefore are real projections with the same total-rank bound. Lemma 7's equal-rank polar completion uses a real partial isometry extended between real orthogonal complements. The final stack/polar estimates use adjoints and positive square roots and retain the constant 9. No infinite-algebra real-form theorem is needed.

## Full normalization and budget calculation

Set S=sum_i A_i, K=sum_i tr(A_i²), T=tr(S²), and O=T−K. Each pair trace is nonnegative, hence O≥0. If S=0 all A_i vanish and any labelled orthogonal decomposition suffices. Otherwise restrict to support(S). Every A_i vanishes on ker(S), so extending a resulting PVM by assigning that kernel to one label changes none of the estimates.

On support(S), put a_i=S^(−1/2) A_i S^(−1/2). These form a POVM. Use the positive normalized state

    phi(X)=tr(S² X)/T.

Define Q=sum_i tr(S² a_i²). In an eigenbasis S=diag(s_u),

    Q=sum_(i,u,v) (s_u/s_v) |(A_i)_(uv)|².

Pairing (u,v) and (v,u) shows Q≥K, since r+1/r≥2. Since 0≤a_i≤I, a_i²≤a_i, giving Q≤T. Thus E=Q−K and D=T−Q are nonnegative and E+D=O. This last exact identity makes the two error budgets compatible.

Let R=sum_i ||A_i−a_i S||_F². For an unordered off-diagonal pair with r=s_u/s_v, the coefficient in R is

    r+1/r−2 sqrt(r)−2/sqrt(r)+2,

and the coefficient in E is r+1/r−2. Their difference is `2(sqrt(r)+1/sqrt(r)−2)≥0`. Diagonal terms vanish. Therefore R≤E without a condition-number factor.

The primary theorem gives a labelled PVM P_i with

    sum_i ||(a_i−P_i) S||_F² ≤ 9D.

The weighted state is exactly what produces this right-multiplication norm; cyclicity of the trace gives the displayed equality of norms. Applying the triangle inequality in the direct sum of Hilbert–Schmidt spaces, followed by Cauchy–Schwarz in two coordinates,

    sum_i ||A_i−P_i S||_F²
      ≤ (sqrt(E)+3 sqrt(D))²
      ≤ 10(E+D)=10O.

For s≠i, P_s(P_i S)P_s=0. The orthogonal diagonal block projections are jointly Hilbert–Schmidt contractive, so

    sum_i sum_(s≠i) ||P_s A_i P_s||_F² ≤10O.

If actual positive orthogonal approximants are desired, take B_i=P_i A_i P_i. Their supports are orthogonal. For Hermitian A_i, the block decomposition gives

    ||A_i−B_i||_F² ≤2||(I−P_i) A_i||_F²
                       ≤2||A_i−P_i S||_F².

Consequently sum_i ||A_i−B_i||_F²≤20O. This is another consequence of the same compatible reduction, not a separate discovery.

The arbitrary-state theorem supplies the needed simultaneous projections; the square-sum state and elementary spectral identities transfer exactly to the source's unnormalized Frobenius overlap. There is no remaining operation in this splitting comparison to nominate. Improving the internal constant does not itself improve the source's exponential PSD-rank scale or create a new matching theorem.

## Why exact preservation of S is a separate boundary

Let 0<e<1, c=sqrt(1−e²), and

    A1=[[1,0],[0,0]],       A2=[[e², ec],[ec,c²]].

Both are rank-one projections. Their overlap budget is O=2e². S=A1+A2 has distinct eigenvalues 1+e and 1−e, with projections Pplus/Pminus=(I±(S−I)/e)/2.

If B1,B2 are positive, B1 B2=0 and B1+B2=S, then S B1=B1²=B1 S. Because S has simple spectrum, each S eigenvector belongs entirely to one B label. Thus B1 is one of 0, S, (1+e)Pplus, (1−e)Pminus; B2 is its complementary part. Direct substitution yields

    ||A1−B1||_F²+||A2−B2||_F²=2

in all four cases. Therefore no absolute multiple of O can control this error while preserving S exactly for all e. This refutes only that additional exact-sum estimate. It is not a refutation of the compatible splitting bound, a new nominated theorem, or a repair of any previously frozen scope.

The rational finite diagnostic chooses e=2t/(1+t²), c=(1−t²)/(1+t²) for t=1/k. The displayed algebra proves the general statement; the diagnostic verifies only the listed finite examples.
