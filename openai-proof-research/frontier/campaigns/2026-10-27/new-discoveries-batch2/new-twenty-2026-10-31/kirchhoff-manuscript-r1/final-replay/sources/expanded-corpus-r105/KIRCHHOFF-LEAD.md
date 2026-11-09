# 349441: exact spectral counterexample, scope and formalization HOLD

No acceptance or novelty clearance is claimed. No Lean endpoint has been proved.

Take K6 on vertices 0,...,5 and attach the path 0--6--7--8--9--10. This is a connected simple 11-vertex graph. Its degrees are 6,5,5,5,5,5,2,2,2,2,1. This is beyond the source's all-connected-graphs experiment through order 8. The exact arithmetic below is independently reproduced by Fraction arithmetic in scripts/verify_kirchhoff.py; the full matrices and characteristic polynomials are in outputs/kirchhoff-certificate.json.

Use the source's (3.8), L_a = diag(c_a) - K^a A K^(-a), with c_a(i) = sum_{j adjacent i}(d_i/d_j)^a. Under Lemma 4.6's spectral index R_a = 11 sum_{nonzero eigenvalues rho} 1/rho, the indices are

* R_1 = 1696684/14035;
* R_0 = 370/3;
* R_-1 = 1096887/11036.

Thus R_0 - R_1 = 102898/42105 > 0, reversing the first inequality in Conjecture 4.13. This is an exact witness for the spectral reading, not a floating point sign discrepancy. Within the tested lollipop family, none at orders 9 and 10 reversed the spectral inequalities; two at order 11 did. No global minimality is claimed.

Ordinary algebraic certificate: let z be the all-ones column and w_i = d_i^(-2a). Let P = z w^T/(w^T z). Then L_a z = 0, w^T L_a = 0, P^2 = P. The supplied matrix G_a satisfies L_a G_a = G_a L_a = I-P and G_a z=0. Equivalently, G_a = (L_a+P)^(-1)-P. The matrix L_a is similar, via K^a, to the real symmetric matrix diag(c_a)-A. That symmetric matrix is positive semidefinite by summing ( (d_i/d_j)^(a/2) x_i - (d_j/d_i)^(a/2) x_j )^2 over edges; connectedness makes its kernel one dimensional. Therefore the spectral group inverse acts by reciprocal on nonzero eigenspaces and by zero on the kernel. Consequently R_a = 11 trace G_a. Independently, if det(XI-L_a)=X(c_0+c_1 X+...), then sum 1/rho=-c_1/c_0. Both computations agree exactly, and the characteristic coefficients were separately checked by the Faddeev-LeVerrier recursion.

Why HOLD: the paper calls L_a^+ the Moore-Penrose inverse (Lemma 4.2), but its proof then treats a nonorthogonal eigenbasis as though Moore-Penrose inversion commuted with similarity (around (4.9)-(4.11)). That identity is false for general nonsymmetric matrices. The source's physical Definition 4.1 uses potentials solving L_a V = I(e_s-e_t), which is not generally solvable for unequal degrees because the left null vector is w, not z. These are real source-semantic issues, not permission to substitute a different definition silently. The true Moore-Penrose reading also has R_1 < R_0 at this witness (exact values retained), but this does not repair the missing physical-potential bridge. The source's own claimed all-graphs computational data should be reconciled against the intended spectral implementation before qualification. No new credit for exposing that generic inverse error is requested.

Source-own-lemma screen: Theorem 3.11 gives the similarity and positivity; Lemma 4.6 gives the spectral trace formula; Lemmas 4.8, 4.9 and 4.11 are absolute lower bounds and do not establish the conjectured ordering when combined. No combination inspected already supplies this lollipop reversal. The ordinary certificate is a new calculation in this lane, not a claim of literature priority.

Remaining work: root statement-fidelity adjudication of the intended spectral resistance reading; primary later-literature and current registry-body comparison; then a full Lean definition of the graph and Laplacians, real diagonalization/group-inverse or characteristic-root bridge, exact certified arithmetic, literal universal-conjecture negation, sanitized strict replay, leanchecker and all-declaration axiom audit. A theorem about the displayed rational numbers alone would be a prohibited surrogate and has deliberately not been offered as an endpoint.
