# A.4 / 339078: flagged identity verified; full positivity unresolved

29 October 2026 UTC (28 October America/Los_Angeles). Credit **0**.
Counts remain 3/30 additional, 33/60 total. No full proof, refutation,
nomination, acceptance authority, or Lean investment.

## Source and public-proof gate

The exact target is Oh–Scrimshaw, *Identities from representation theory*,
arXiv:1805.00113v1, Appendix A, Conjecture A.4: for every n,k>=1,
Delta_n^(2k)=det(M_(i+j+2k))_(0<=i,j<n) has nonnegative integer coefficients,
where M_0=1 and M_(m+1)=M_m+sum_(a=0)^(m-1)q^(a+1)M_a M_(m-1-a).
The actual Appendix and source recurrence were read, and the entire source
HTML freshly downloaded at 2026-10-29T05:54:16 UTC; its SHA256 matches r3.
The journal body remains uncleared. This report does not narrow the target.

Before significant calculation I read the root adoption and r2/r3 discovery
reports, ledger and prior-campaign context, and screened the permitted recent
complete registry trees from sol-fresh-analysis-discovery-r7. Coverage is
explicitly **2026-10-29 04:39–04:43 UTC**, not a new head retrieval:
trureturing 67b4fae085cf19003a33f8027410c383b49e5046,
count-ex-machina dbf673741a54c7dc9d88a6aec0e8148a538f4a3a,
openai/math 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a.
Problems/D5/preprints trees are untruncated. The actual sibling 339076 body
expressly excludes positivity A.4; its printed shift-2 factorization refutation
is not this target. Prior r2 body comparisons distinguish Cigler's boundary
weights, Barnabei et al.'s unshifted moment result and Miller–Stanton's Smith
form. R3 distinguishes complex-parameter q-Lommel from positive-real measure
results. These remain bounded comparisons, not comprehensive novelty clearance.
Current public search returned the indexed literal MathDB339078 statement and
no located full proof. An open label is not evidence of novelty. No GitHub API
traversal was repeated; known GitHub rate limits and direct MathDB403 were
respected without retries or alternate host/API attempts.

## The flagged identification is valid, with no reversal sign

Let r=2k, t=q^(-1), omega^2+omega+1=0, omega!=1, and put
X_(2l+1)=omega t^l, X_(2l+2)=omega^2 t^l, 0<=l<r.
R3's exact coefficient formula gives

 C_(i,m)=t^binom(i,2) [z^(m-i)] product_(l=0)^i(1+t^l z+t^(2l)z^2)^(-1).

Since (1-omega z)(1-omega^2 z)=1+z+z^2, it follows in Z[omega,t] that

 C_(i,m)=t^binom(i,2) h_(m-i)(X_1,...,X_(2i+2)).                 (1)

Use Wachs, JCTA40(1985)276–289, equation(1.1), tableau definition on
printed p277, Theorem1.3 and its inductive proof on pp278–280. The actual PDF
was read, including visual inspection of p277. Her shape parts decrease,
flags weakly increase, rows weakly increase, columns strictly increase.
The determinant index is lambda_a-a+b (one-based), with the alphabet bound
b_a on ROW a. Here lambda=(n^r), a=i+1, b=j+1, flag_a=2a, giving exactly
n-i+j. Consequently

 det C_(i,n+j)_(0<=i,j<r)
   = t^binom(r,3) S_((n^r),(2,4,...,2r))(X).                  (2)

There is no transpose, row reversal, negative partition, or hidden sign.
Together with the complete r3 Christoffel bridge,

 Delta_n^r = q^(sum_(i<n)i^2 + sum_(j<r)binom(n+j,2))
                  det C_(i,n+j)(q^(-1)),                    (3)

this is an exact equivalent formulation of A.4 for every even r. It supplies
no coefficient positivity by itself: the X's are complex monomials.
This use of a classical determinant theorem is uncredited.

## Closest root-of-unity theorem does not apply directly

V. Sathish Kumar, arXiv:2306.10289v1 (17 June2023), actual Sections1–4,
especially Theorem1, definition of phi_d, Lemma1, Theorem4 and its proof,
was read before the cancellation work. Theorem4 factors flagged skew Schur
polynomials when both flags are divisible by d, under substitution by COMPLETE
d-tuples (y,eta y,...,eta^(d-1)y). The proof uses the vanishing of h_j unless
d divides j, then regroups determinant indices modulo d.

Our d=3 alphabet omits y from every triple, and flags2,4,... are not all
multiples of3. Its first pair already has h_1(omega,omega^2)=-1, violating
the zero premise used in that block decomposition. d=2 would require opposite
letters, whereas omega^2/omega=omega!=-1. Padding the missing real letters
by zeros does not yield a complete triple with the other two letters nonzero.
Thus neither that theorem nor its Demazure corollary directly supplies the
claim. This is not a proof that every possible virtual-alphabet transformation
or another character theorem fails to subsume it; no blanket novelty clearance.

## What conjugation symmetry really proves

For each flagged tableau T let
 A(T)=sum_cells floor((T_cell-1)/2),
 R(T)=sum_cells (1 if T_cell odd else 2) modulo3.
Let N_s(d) count tableaux of area d and residue s. Its specialized weight is
omega^R(T)t^A(T). All alphabets in every row of (2)'s determinant contain
complete pairs. Swapping X_(2l+1),X_(2l+2) therefore fixes each determinant
entry, hence fixes S. Swapping every pair conjugates omega and preserves t.
Writing S=sum_d(N_0+omega N_1+omega^2 N_2)t^d, equality with its conjugate
implies N_1(d)=N_2(d) (omega-omega^2 is nonzero). Therefore

 [t^d]S = N_0(d)-N_1(d).                                    (4)

Symmetry proves integrality, not the needed inequality N_0(d)>=N_1(d).
It can also be realized by the usual two-letter tableau involutions: pair
vertical occurrences, then interchange numbers of unpaired letters in each
row. No even flag separates the two letters, so these preserve our flags.
No claimed positive trace or positive-character argument fills (4).

## Exact obstruction to cancellation within fixed pair-position classes

Group tableaux by the positions occupied by each pair {2l+1,2l+2}.
Equivalently, fix the nested shapes mu^(l) of cells with entries <=2l,
mu^(0)=empty, mu^(r)=(n^r). The row flags require the top l rows of mu^(l)
to be full; columns impose the usual two-letter feasibility on each layer.
Once this chain is fixed, fillings of its successive skew layers are independent.
Comparisons between different layers hold automatically because their entries
are strictly ordered. Its weight generating polynomial is exactly

 product_(l=1)^r s_(mu^(l)/mu^(l-1))(X_(2l-1),X_(2l)).          (5)

A layer with >2 cells in some column has no filling. Otherwise let V be its
number of double columns and L_i the number of remaining single cells in row i.
The double columns force upper1/lower2. For a skew partition diagram those
forced1's lie to the left of the unpaired upper-row cells, and forced2's to the
right of the unpaired lower-row cells. Hence all unpaired weak binary strings
are free independently, proving the elementary two-letter formula

 s_(nu/mu)(x,y)=(xy)^V product_i h_(L_i)(x,y).                 (6)

At x=omega a,y=omega^2 a, the degree-L factor is a^L times 1,-1,0 as
L=0,1,2 modulo3. This follows directly from
sum h_L(omega,omega^2)z^L=(1-z)/(1-z^3).
Thus an individual class can be a negative monomial, even for our exact even
rectangle and exact flags, not only for an unrelated arbitrary shape.

Take n=4,r=6 (k=3) and this chain, zero parts shown:

 mu1=(4,0,0,0,0,0)
 mu2=(4,4,3,0,0,0)
 mu3=(4,4,4,2,1,0)
 mu4=(4,4,4,4,3,2)
 mu5=(4,4,4,4,4,3)
 mu6=(4,4,4,4,4,4).

Every row flag is satisfied. The six layers have double-column counts
0,3,1,2,0,0, and nonzero free lengths respectively
(4), (1), (1,1), (1,1), (1,1), (1).
Their signs are -,-,+,+,+,-, with product -1.
Their sizes are 4,7,4,6,2,1, so their area is
0*4+1*7+2*4+3*6+4*2+5*1=46. This class contributes **-t^46** to S.
Equivalently it contains exactly (N0,N1,N2)=(426,427,427) tableaux.
For a direct count, its forced pairs contribute residue0; its free generating
factor is h4(omega,omega^2)h1(omega,omega^2)^8. Before root reduction h4 has
residue counts(1,2,2), and h1^8 has(86,85,85), giving the displayed counts.
Thus this finite obstruction is proved by formulas and exact counts, not
inferred from sampling. For det C the row monomial shifts this to -t^66.

This excludes a mechanism that makes EACH fixed pair-position class positive
by cancellation confined to that class, including mere pairwise letter
symmetry. It is **not** a counterexample to A.4, to independent pair-content
positivity, or to all possible character decompositions. In fact, summing all
chains with this SAME pair-content profile gives coefficient0, as the bounded
checker confirms. Cancellation across different chains can already repair it
without changing the profile. No assertion about the full t^46 coefficient is
made. No further source determinant positivity grid was produced.

## Validation and remaining gap

`python check.py` sets 512MiB RLIMIT_AS, 45s CPU deadline and BLAS/OMP/MKL
threads1 before algebra imports. It independently enumerates each of the six
binary skew layers, verifies the residue counts, computes the single fixed
profile sum over partition chains, verifies21 coefficient identities between
the predecessor recurrence and finite-product extraction, and compares one
small flagged determinant with a direct tableau sum. These are exact formula
and obstruction checks, not numerical proof of A.4. All pass; no resource
limit was raised, no diagnostic failure suppressed. `fetch.py` downloads the
three primary bodies once each, recording date/status/hash and any failure.

The strongest objection is that (1)–(6) are classical or elementary helpers,
and the negative class only disproves an overly local sufficient strategy.
The full claim is still precisely the all-n,k,d inequality N0(d)>=N1(d),
or an exact violating coefficient of the required full determinant. A uniform
cross-chain injection, positive character/network decomposition after the
complex specialization, or source refutation has not been obtained.
No PROOF.md, Lean work, paper or acceptance request is justified.
