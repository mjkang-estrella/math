# Infinite physical channels: feasibility, before selection

No theorem was frozen here. This is a compatibility calculation for the source262 equality proof, not an independently reviewed infinite-channel classification or a nominee. The finite-dimensional source is stipulated, including its quantitative action operation. The point is to check its strongest actual reduction before treating its finite-column hypothesis as an unpaid mechanism.

## Exact source contracts

In the equality companion, `act:quantitative-action` accepts every finite number n of trial rows and every finite number d of physical columns. Its c_*(sigma,kappa)>0 is independent of BOTH n and d, the smallest binding energy, interval and trial family. It supplies a lower-triangular coefficient matrix C, a bounded symmetric path B and the integrated errors

    ||A'-BA||_HS^2,
    min(1, ||[B,K^2]||_op^2 + ||K^2-B^2-(AA*)^r||_op^2).

Here p=gamma+1/2 in (1,2), r=1/(p-1)>1, q=r+1=p/(p-1), and A=CU. The source `comp:triangular-gap` suppresses coefficients between distinct binding energies; `comp:common-shift` preserves all squared-energy differences. Those are already paid operations. Reading the theorem and its complete action proof confirmed that the constant is not merely independent of the eigenfunction count.

The actual compactness proof uses the finite physical dimension m twice: it bounds the Hilbert--Schmidt L^(2q) norm of A by m^(q-1) tr((A*A)^q), and turns an operator-norm tail bound into a Hilbert--Schmidt tail bound by multiplying by m. Neither step should be asserted in an infinite physical space.

## The stronger compatible replacement

Work temporarily with the SAME finite trial approximations as the source, now taking values in finite-dimensional subspaces of a fixed separable real Hilbert space H. A finite collection in H^1(R;H) can be approximated by smooth compactly supported functions with values in a common finite-dimensional subspace; Gram--Schmidt retains this property. The source action therefore applies without changing its constant. No infinite-dimensional connecting-path theorem is being presumed.

Suppose the source equality-defect construction has produced its finite-rank A_j, B_j, K_j with the same vanishing errors and fixed-row convergence. Let W>=0 be fixed with W in S_p at the point in question, and put Z_j=A_j* A_j. The source Young deficit is

    Y(W,Z_j)=D tr(W^p)-tr(W Z_j)+tr(Z_j^q),
    D=(p-1)^(p-1)/p^p.

It makes sense for W in S_p and finite-rank Z_j. The same scalar scaling and trace Holder inequality give

    Y(W,Z_j) >= (1/2) tr(Z_j^q) -(2^(p-1)-1)D tr(W^p).

This is dimension independent. In particular a fixed row satisfies

    ||(A_j)_i||_H^2 <= ||A_j||_op^2
       <= (tr(Z_j^q))^(1/q).

Integrating this last bound on the finite Gram-control interval J_i replaces the source's m-dependent bound. The same finite lower-triangular Gram argument bounds every fixed row's coefficients; convergence in H^1(R;H) then follows as in the source. This checks the fixed-row premise without any uniform Hilbert--Schmidt norm for the full A_j.

At a point where the errors vanish, let Lambda=diag(k_i), P_h be the first-h-row projection, Q_h=I-P_h, s_h=sup_(i>h) k_i^2 and

    e_j=||K_j^2-B_j^2-(A_j A_j*)^r||_op ->0.

The source's positive quadratic estimate and spectral Jensen inequality already imply

    ||Q_h A_j||_op^2 <= (s_h+e_j)^(1/r),
    ||B_j Q_h||_op <= (s_h+e_j)^(1/2).

The first estimate is obtained BEFORE the finite-rank trace estimate in `comp:tail-bounds`. For fixed h, convergence of h rows as H-valued vectors is convergence of P_h A_j in operator norm. The displayed tail bound therefore makes A_j Cauchy in operator norm. Its limit A is compact, as a norm limit of finite-rank operators. The finite-row compressions of B_j, and the second tail bound, give a pointwise subsequence converging in operator norm to B. Thus

    [B,Lambda^2]=0,
    Lambda^2-B^2=(AA*)^r,
    a_i'=(BA)_i

pass to the limit. The pointwise B subsequence need not be measurable, exactly as in the source. Functional calculus here is operator-norm continuous on a common bounded positive interval. No Hilbert--Schmidt convergence is used or inferred.

The last interface is the Young equality. Write Z=A*A. Operator-norm convergence gives Z_j->Z. The coercive estimate bounds ||Z_j||_S_q at each such point. Lower semicontinuity of the q-power trace follows by summing the first N eigenvalues and then letting N grow. Hence Z belongs to S_q. For a finite-rank approximation W_N to W in S_p,

    |tr((W-W_N) Z_j)| <= ||W-W_N||_S_p sup_j||Z_j||_S_q,

and the finite-rank W_N pairing converges by operator-norm convergence. Consequently tr(WZ_j)->tr(WZ). It follows that

    0 <= Y(W,Z) <= liminf_j Y(W,Z_j)=0.

The zero-deficit identity is W=q Z^r. It can be checked without inventing a new compactness theorem: use orthonormal eigenbases of the two positive compact operators and expand the trace pairing. The deficit is the sum, with weights |<e_i,f_j>|^2, of scalar nonnegative Young deficits D w_i^p-w_i z_j+z_j^q. Equality forces w_i=q z_j^r whenever the overlap is nonzero; zero eigenspaces are included. This gives exactly W=qZ^r. All power traces and pairings converge by the stated Schatten assumptions, and the nonnegative scalar sum permits Tonelli.

This is the missing CHECK in the earlier r114 screen, but it is a compatible use of the source's existing operator-norm defect plus classical trace duality and lower semicontinuity. It supplies no separately identified unpaid operation. Merely saying that finite equality does not pass through arbitrary approximations would miss this stronger source interface.

## What the fixed-channel part already does

Every positive eigenvalue of the compact negative part has finite multiplicity. Thus each source block G_alpha still has finitely many rows, even if H is infinite dimensional. For each v in H, ||(G_alpha v)'||<=kappa||G_alpha v|| preserves its kernel by Gronwall. Its orthogonal-complement row space has finite dimension at most the eigenvalue multiplicity and is constant. Different alpha blocks are orthogonal. The source's fixed-left-space projection and finite matrix Riccati equation operate on these finite spaces unchanged. There can now be countably many blocks; there is no assertion that their total dimension is finite. A bounded-operator tail is controlled by q alpha^2, which tends to zero. This identifies the compatible way to reuse the source rigidity, rather than discarding its rank argument without replacement.

An instructive diagnostic is gamma=1, r=2 and countably many centered solitons with a_j=1/j. Their trace-p cost is proportional to sum j^-2, while the density Z(0)=q^(-1/r)W(0)^(1/r) has trace sum j^-1=+infinity. Thus the infinite-channel setting can really require a non-Hilbert--Schmidt A. A proof that silently keeps the finite-column HS conclusion would be wrong. This example is a method diagnostic, not a nominated theorem.

## Primary and historical comparison

Laptev--Weidl, [math-ph/9903007v2](https://arxiv.org/pdf/math-ph/9903007v2), §2.2 and the entire Theorem2.1 proof in §2.3, already treat compact operator potentials by finite physical projections, form control and finite negative-spectral subspaces. Their exponent is 3/2, but the projection argument itself accepts any supplied dimension-uniform finite-matrix moment bound. It supplies the natural inequality reduction; it does not assert the open-interval equality classification.

Read--Schulz, [2609.10478v2](https://arxiv.org/pdf/2609.10478v2), Proposition4 and equation(2.1), already work with an arbitrary separable physical Hilbert space at gamma=1. Their finite trial-index Gram matrix, square completion and trace duality are the relevant interfaces. Sections 2.1–2.2, including Lemma6's positivity proof, were subsequently read completely before sealing. No extension of that primary to other exponents independently is claimed. External primaries are not covered by the upstream truth stipulation.

The actual r114 `operation-comparison.md` already raised infinite-channel equality as an unchecked interface. I250/I264/I271 rotating-channel stability is a different old direction, and is not reopened. The full source compactness/action/rigidity bodies, rather than that summary, supplied this feasibility test. No target was frozen before or after it; no full equality theorem is presented for a gate. There is no claim of worldwide duplication, priority clearance, or an independent correctness/contribution verdict.
