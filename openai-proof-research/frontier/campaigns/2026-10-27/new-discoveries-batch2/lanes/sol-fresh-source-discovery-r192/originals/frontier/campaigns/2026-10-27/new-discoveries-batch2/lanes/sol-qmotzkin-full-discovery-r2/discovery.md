# Full A.4 investigation: no qualifying resolution

Date: 2026-10-29 UTC (2026-10-28 America/Los_Angeles). Solo research; credit 0;
no acceptance authority. Target is exactly Oh–Scrimshaw arXiv:1805.00113v1,
Appendix A, Conjecture A.4 / MathDB339078: for every n,k >= 1,
Delta_n^(2k) = det[M_(i+j+2k)(q)]_(0<=i,j<n) belongs to Z_nonnegative[q],
where M_0=1 and M_(m+1)=M_m+sum_(r=0)^(m-1) q^(r+1)M_r M_(m-1-r).
No proof or counterexample to that assertion was obtained. All partials below
are uncredited route diagnostics, not candidate discoveries.

## Source and prior-proof checks before new computation

Read root and campaign AGENTS, ledger, NEXT, prior-campaign-context,
root-qmotzkin-adoption-r1/ADOPTION.md and the original Pi SUMMARY, discovery,
progress and ordinary proof report. Root's corrections supersede the Pi claims:
shift2 is routine/uncredited; mixed T-minor is k3, not k2; old Lean fails.
Cached source.txt Appendix A was read, and the 4,471,871-byte original HTML was
processed with bounded extraction, not printed as its huge single line. A fresh
public HTTP fetch on 2026-10-29 returned the identical SHA256
 ec9caeb98eab3d3c309a3c4f3f509dc827a1779b798426182135b73fb19e830a.
The journal version of Identities from representation theory was not obtained;
no journal-body or universal novelty clearance is claimed.

Reused complete untruncated recent registry trees and head receipts in
sol-fresh-analysis-discovery-r7 (04:39–04:43 UTC October29). No GitHub API requests.
The omega Problems/D5 paths matching Motzkin were screened; the actual pinned
Oh–Scrimshaw sibling refutation and both Cigler boundary/column problem bodies
were freshly read from raw GitHub at head67b4fae085cf19003a33f8027410c383b49e5046.
The sibling resolves only the printed shift2 factorization /339076. The Cigler
bodies concern constant-above-boundary weights and recurrence denominators,
not a resolution of this geometrically height-weighted even-shift question.
OpenAI preprint paths and count registry did not locate an exact counterpart.
This is a bounded path/body screen, not a proof that all registry source bodies
lack an answer. Heads were not refreshed after those recent receipts.

Targeted public searches located the current MathDB339078 indexed statement,
which agrees with the target; its open label is not novelty evidence. MathDB
was not directly requested because the preceding lane recorded host403.
Search readback is indexed evidence only, not current solution-array clearance.
No public proof of full A.4 was identified in this bounded search.

## Closest actual primary bodies

1. Barnabei–Bonetti–Castronuovo–Silimbani, Motzkin and Catalan Tunnel Polynomials,
JIS21(2018), Article18.8.8, actual publisher PDF,
https://cs.uwaterloo.ca/journals/JIS/VOL21/Barnabei/barnabei5.pdf .
Read Section2 (especially2.2(f),2.3, printed pp7–9), and the later Hankel
Theorem15 and its proof. Section2.2(f) already gives the area specialization
MT_n(1,1,...;q,q^2,...;1); Section2.3 gives the exact Jacobi fraction with
b_h=zq^h and lambda_h=q^(2h-1). At z=1 these are our moments. Its Hankel result
is the unshifted determinant q^[n(n+1)(2n+1)/6] for size n+1, not full A.4.
Theorem15 instead concerns partial/free path polynomials with constant weights.
Thus the old Pi description of the area/J-fraction bridge as new is unsupported.
No full even-shift theorem occurs in these read determinant passages. This is
not a claim to have checked all later citations or the target's journal changes.

2. Miller–Stanton, Orthogonal polynomials and Smith normal form, actual author
PDF https://www-users.cse.umn.edu/~stant001/PAPERS/StantonMillerFinal.pdf .
Read Section3/Theorem1 and proof, Section4.2/Corollary3, and the scope of the
later results. Theorem1 gives unshifted moment-Hankel Smith form via monic
orthogonal-basis congruence. It supplies no coefficientwise positivity for the
shifted Gram determinant L(x^(2k)p_i p_j). Section4.2's named q-Motzkin family
has b_h=1, lambda_h=q^(h-1), which differs from b_h=q^h,
lambda_h=q^(2h-1). General Theorem1 covers our unshifted specialization, but
Corollary3 is not a same-object even-shift theorem. No new positivity premise
can be supplied merely by invoking Smith form.

## Exact all-parameter signed expansion and its obstruction

Use the root-adopted reduction B=KD, D_hh=q^h,
K_hj=1_(|h-j|<=1), beta_n=sum_(i<n)i^2:
 Delta_n^(r)=q^beta_n det((B^r)_[0,n)).
For the even power 2k, restrict heights to 0,...,n+k-1. This is exact: a walk
starting and ending below n, of length2k, has height at most n-1+k. In the
compound-matrix version every allowed matching moves a height by at most1;
therefore the same bound follows by distance from both endpoints.

Let I={0,...,n-1}. Cauchy–Binet at each time gives the exact signed formula
 det((B^(2k))_I) = sum_(A_0=I=A_(2k))
    product_(t=1)^(2k) det(K_[A_(t-1),A_t]) q^(sum A_t),
where each A_t is an n-subset of those finitely many heights. Consecutive-ones
TU gives each determinant in {0,+1,-1}. It does not make the closed walks
positive. This formula identifies the missing full mechanism precisely:
for every area a, the signed sum over closed compound walks of total area a
must be nonnegative. Neither TU nor reversibility alone proves this.

A concrete even negative loop excludes any attempt to repair all signs by a
diagonal sign gauge (including on the parity double cover):
 012 -> 012 -> 023 -> 013 -> 024 -> 023 -> 012.
Its six K-minors have product -1. A gauge's vertex signs cancel around a closed
even loop, so this obstruction is invariant. This is a route obstruction,
not a negative final q coefficient: other loops at the same area can cancel it.

More decisively, even the fully summed determinant is NOT coefficient-positive
with independent height weights. For D=diag(d0,...,d5), n=3, k=3, the coefficient
 [d0^6 d1^3 d2^5 d3^2 d4^2] det(((KD)^6)_[0,3)) = -4.
There are192 nonzero monomials,10 negative. `compound.py` computes them via20
states and6 time layers; `independent.py` independently multiplies the ordinary
3-by-6 row block of B six times and expands the 3-by-3 determinant. They agree
on every negative coefficient and on the entire q-height specialization.
This finite block equals the infinite half-line result by the preceding height
bound. Thus the counterexample is exact, not a truncation artifact.

At d_h=q^h this negative monomial has degree27. All monomials of degree27
instead sum to +30. It is the geometric identification of distinct occupation
vectors that rescues this coefficient. Any all-k proof based only on independent
nonnegative level variables is therefore false; a proof must exploit that
identification or a stronger source-specific structure. As a univariate
counterexample to the stronger arbitrary-height assertion, substitute d_h=z^(7^h):
base7 uniquely encodes exponents0..6, and the coefficient at z^5760 remains -4.
This says nothing negative about the required substitution d_h=q^h.

## Toda/cluster route: exact missing hypothesis

Desnanot–Jacobi gives
 Delta_n^(r+1) Delta_n^(r-1) =
 Delta_(n+1)^(r-1) Delta_(n-1)^(r+1) + (Delta_n^r)^2.
The known shift0 column is monomial, enabling the routine shift2 result.
Higher odd columns are not signed positive polynomials. Directly from the
literal recurrence, Delta_3^5 starts -q^38+2q^34+6q^33+..., and its square
has coefficient -4 at q^72 (also nine other negative coefficients).
`toda_obstruction.py` records the full exact polynomial and square, and checks
that direct source Delta_3^6 agrees with the compound specialization times q^5.
Consequently the odd square is not an admissible positive polynomial seed.
A generic Laurent-positivity assertion would require an actual seed with
nonnegative monomial substitutions and denominators; no such seed or bridge
was established. Known shift1 constants include negatives and zeros, so they
cannot simply be substituted into an invertible positive initial cluster.
No cluster theorem is asserted to resolve or subsume A.4.

## Bounded validation and precise endpoint

`check.py`: exact ZZ[q] transfer multiplication and fraction-free Bareiss
elimination, all56 pairs 1<=n<=7,1<=k<=8. Every resulting even-shift polynomial
has nonnegative coefficients. This extends the earlier diagnostic range but
is no theorem and no credit. Five nongeometric one-variable specializations
also stayed positive; the independent-variable calculation demonstrates why
those samples cannot support the stronger invariant.

Every mathematical executable sets address-space limit512MiB, CPU limit30/60/90s
and BLAS/OMP/MKL thread count1 before importing algebra code. No Lean was run:
there is no complete eligible ordinary candidate to formalize. There is no
PROOF.md, full theorem, refutation, paper, acceptance recommendation or count
change. The exact remaining obstruction is uniform nonnegativity of the
area-grouped signed compound-walk sums for every n,k. No uniform injection,
involution, positive seed or closed formula for those sums was found.
