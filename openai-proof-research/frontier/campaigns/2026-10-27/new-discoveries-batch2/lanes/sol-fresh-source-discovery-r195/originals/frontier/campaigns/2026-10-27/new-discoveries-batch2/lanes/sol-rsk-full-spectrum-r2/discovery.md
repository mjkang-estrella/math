# Full RSK spectrum question: unresolved; universal mod-2 route is false

Solo research delegate; no acceptance authority. Work on 2026-10-29 UTC
(October 28 in Los Angeles). Credit 0; counts unchanged 3/30 additional,
33/60 total. No complete ordinary candidate, PROOF.md, or Lean endpoint.

## Exact source and eligibility

Stelzer–Yong, *RSK as a linear operator*, Conjecture 5.8, arXiv:2410.23009;
Selecta Mathematica 32, article 88 (2026), DOI
https://doi.org/10.1007/s00029-026-01191-5 . For every positive composition pair
sigma, pi of degree d, normalized as in Assumption 1.3, reduced means
max(sigma)+max(pi)<=d. Triangular means len(sigma)=2 and sigma_1=pi_1.
For every reduced nontriangular pair the conjecture asserts that its literal
RSK weight operator has a noninteger eigenvalue. The operator sends the
monomial of a contingency table to the product of minors of its RSK tableaux;
input biletters are read down columns, left to right, with strict-greater
row bumping. No endpoint, zero-margin, domain, or normalization correction
is proposed. MathDB365595 is only a target identifier.

Read the predecessor sol-fresh-discrete-discovery-r9 reports, source/derivation
and all five diagnostic scripts before selecting this continuation. Its
second-moment counterexample, failed cycle inheritance and multiplication
embedding remain valid route exclusions. Read the actual cached original
and journal statement bodies, and Zhang's entire six-page proof, especially
Proposition 4.1's four insertion cases and the integral basis change in
Lemma 2.2. Phan–Xia's actual Theorems 1.2–1.3 and Corollary 2.6 concern the
already-public zero-density Conjecture 8.7; excluded. Zhang's Sym^2-cycle
family is already public October 26, 2026; excluded. Nothing below is
nominated as a new spectral family.

Chronology: campaign instructions/ledger/context and r9 were read first;
the other relevant lane histories were revisited after the initial targeted
calculations. The first combined ledger/context display was truncated;
compact structured entries were subsequently inspected. The live arXiv abstract
was fetched at 05:17:08 UTC and revealed v2, submitted December 20, 2024
17:19:45 UTC. Its actual body was then retrieved at 05:17:43 UTC. Definitions
1.7/4.4 and Conjecture 5.8 agree with the cached v1 and actual publisher body.
This latest-version check occurred after the first route counterexample,
not before it. No significant formal investment occurred.

## Decisive obstruction: non-unipotence modulo 2 is not universal

The predecessor's finite checks involved 2x3 and 3x3 weights. Their conclusion
was only evidence. The proposed all-margin strengthening is false already at

    sigma=(6,2), pi=(2,2,2,2), N=10.

This is source-valid, positive, reduced (6+2=8) and nontriangular (6!=2).
Direct literal insertion and integer minor expansion give

    chi_T(t)=(t-1)^3(t+1)^3(t^2+1)^2=(t^4-1)^2(t^2-1),
    T^4=I over Z.

Consequently chi_T modulo 2 is (t+1)^10 and (T+I)^4=0 over F2.
It is unipotent modulo 2, while its characteristic-zero spectrum includes
+i and -i. This is NOT an integer-spectrum counterexample to Conjecture 5.8.
The full basis and matrix are retained in checks.json and recomputed by
check.py. Orientation/basis order does not affect the polynomial or identity.

This is also an infinite, already-public structural obstruction, rather than
an isolated diagnostic. Zhang's Proposition 4.1 identifies the actual operator
at ((2n-2,2),(2,...,2)) with Sym^2(B_n). Lemma 2.2's cumulative-sum change of
basis is integral unimodular; its inverse is consecutive differences. Thus
Sym^2(B_n) is integrally conjugate to the symmetric square of an n-cycle.
For even n the actual Theorem 1.1 polynomial is

    (t^n-1)^(n/2) (t^(n/2)-1).

Take n=2^r, r>=2. In characteristic 2 it becomes (t+1)^(n(n+1)/2),
and T^n=I implies (T+I)^n=0. Over C every n-th root occurs, including
noninteger roots. All these pairs are reduced and nontriangular. Therefore
no proof of the full claim can establish the proposed universal F2
non-unipotence statement. This conclusion is a routine consequence of a
public excluded family and earns zero discovery credit.

The failure is on the equality boundary of reducedness, which the full
conjecture explicitly includes. It cannot be discarded as a domain correction.
The two deliberately chosen neighboring strict-interior cases ((5,3),(2^4))
and ((4,4),(2^4)) are nonunipotent modulo 2, with exact characteristic
polynomials retained. These two diagnostics do not establish any interior
classification or justify more range enumeration.

## What Frobenius actually provides, in arbitrary dimensions

Here is a complete elementary helper, not a source resolution or credited
result. For arbitrary finite m,n, any nonnegative integer exponent matrix A,
and any positive integer k, let D_k replace every tableau entry by k adjacent
copies in its row. Then

    RSK(kA)=(D_k P,D_k Q) if RSK(A)=(P,Q),
    T(z^(kA))=T(z^A)^k as integer polynomials.

Proof. Process the ordered biletters of A. In kA each biletter is processed
k consecutive times. Initially each row of D_k P has each label in a number
of occurrences divisible by k. Inserting k copies of a label v either appends
k copies, or replaces exactly k copies of the least label w>v: that label's
multiplicity was at least k, and the newly inserted v's cannot be bumped by
another v. In the latter case exactly k copies of w are bumped to the next
row. Repeating the same argument in each row shows that the updated insertion
tableau is D_k of the ordinary single-insertion result. The k new boxes are
adjacent in the same row, all recording the same column label; hence the
recording tableau also dilates. Induction on the biletters proves the first
identity. Under D_k each original column of both tableaux is repeated k
times. The defining minor product is therefore raised to the kth power,
proving the second identity. This proof has no two-row restriction.

Over F_p, with p prime, Frobenius F:f->f^p is an injective F_p-linear map
from the (sigma,pi) weight space into the (p sigma,p pi) weight space. The
monomial identity and the freshman's dream give T F=F T. Thus the image is
T-invariant, and

    chi_(sigma,pi)(t) divides chi_(p sigma,p pi)(t) in F_p[t].

To justify divisibility, extend an image basis to a basis of the larger
finite-dimensional space; its matrix is block triangular with the smaller
matrix as a diagonal block. Consequently nonunipotence is inherited under
common p-scaling. For p=2 this reduces the sufficient test along common
powers of two in all margins. Reducedness and nontriangularity are preserved
under scaling. It supplies neither the primitive-margin base cases nor a
converse from larger weights. It is compatible with, and does not repair,
the public unipotent family above. Numerical checks of 2x3, 3x3, and 4x4
inputs in structural_check.py are validation of implementation only; the
ordinary argument above supplies the quantified helper proof.

## Exact strict-interior obstruction to residual-monomial factorization

An attractive next step would write exponents as a parity residue plus twice
another table and extend Frobenius by T(z^R f^2)=T(z^R)T(f)^2. This is false,
even with the final margins strictly interior.

Over F2 put x_j=z_(1j), y_j=z_(2j), D_ij=x_i y_j+x_j y_i and

    f=x_2^3 x_3^2 y_1^4 y_2.

Its margins are ((5,5),(4,4,2)). Literal insertion and expansion give

    T(x_1 f^2)+x_1 T(f)^2 = x_3 D_12^7 D_13^2 D_23 != 0.

The final input exponent table is [[1,6,4],[8,2,0]], with margins
((11,10),(9,8,4)), degree21 and 11+9=20<21; it is nontriangular too.
T(x_1)=x_1, so this falsifies exactly the proposed residual-factor formula.
The right side is nonzero because F2[x,y] is a domain and every displayed
factor is a nonzero polynomial. interior_check.py checks all 32 monomials
exactly, not via evaluation. It uses the predecessor's independent direct
insertion and greedy formulas, and the new generic insertion implementation
independently validates Frobenius examples of up to four rows. No assertion
that the residual-factor obstruction itself is new to literature is made.

## Exact remaining obstruction and decision

A full answer still needs either a source-valid integer-spectrum block or a
uniform characteristic-zero exclusion of (T^2-I)^N=0 for all positive reduced
nontriangular pairs. The necessary F2 condition can no longer serve as that
uniform exclusion. One could separate the public unipotent families and
seek another invariant, but no classification of all mod2-unipotent weights
has been proved. Frobenius inheritance alone covers only common scaling,
not arbitrary margins. The explicit residue failure rules out the simplest
binary-factor extension. Known cycle families, ordinary spectral reductions,
helper proofs and fixed instances remain uncredited. No full ordinary proof
means no major Lean work is justified; no conditional lemma is packaged as
a literal source endpoint.

## Provenance, validation and limits

provenance.json records actual source URLs, SHA256s, live receipts, cached
registry heads, input hashes and chronology. Reused the designated complete
recent registry trees; made no GitHub API requests. Their path hits include
only unrelated RSKMinimumInversion/Hankel material, whose actual cached Lean
body was inspected. No full-text registry absence or newer head is claimed.
The direct MathDB403 and GitHub API rate limit remain access gaps; neither
host was retried. Live title/spectral searches found the publisher, original,
Phan–Xia and Zhang; they do not give worldwide novelty clearance. Zenodo's
fresh metadata agrees with the cached PDF's size and publication chronology.
The latest arXiv body and publisher comparison do not establish absence of
all later proofs. No publication, upload, contact, account action or browser
tab occurred; no children, git, shared or other-lane edits.

Run from this directory with Python3/SymPy1.14:

    python check.py
    python structural_check.py
    python interior_check.py

All import prior_check.py before SymPy: hard address-space cap512MiB,
hard CPU120seconds, BLAS/OpenMP/MKL/NumExpr1. Only four preselected weight
blocks are built (dimension<=19); generic inputs have <=4 rows/columns and
degree<=20, <=10,000 retained terms and <=1,000,000 expansion operations.
The interior polynomial has degree21 and exactly32 terms. All loops have
explicit finite bounds; no broad/exponential search, floating eigenvalues,
or new fixed-range survey. Existing source-table implementation checks are
preserved in the read-only predecessor, not rerun into that lane.
