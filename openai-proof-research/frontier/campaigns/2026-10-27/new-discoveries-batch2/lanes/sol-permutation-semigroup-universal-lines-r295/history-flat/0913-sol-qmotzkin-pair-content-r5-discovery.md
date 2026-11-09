# Pair-content positivity fails; literal A.4 remains open

29 October 2026 UTC (28 October in America/Los_Angeles). Credit 0; counts
3/30 additional and 33/60 total unchanged. No acceptance authority.

## Target and source gate

The literal target is Oh–Scrimshaw, arXiv:1805.00113v1 Appendix A Conjecture
A.4 / MathDB339078: for all integers n,k>=1,
Delta_n^(2k)=det(M_(i+j+2k)(q))_(0<=i,j<n) belongs to Z_nonnegative[q],
where M_0=1 and
M_(m+1)=M_m+sum_(a=0)^(m-1)q^(a+1)M_a M_(m-1-a).
I read the actual Appendix recurrence and A.4 from the r4 cached primary
body, and the r3/r4 discoveries and root adoption corrections before work.
The journal version remains uncleared.

Wachs, JCTA40(1985)276–289, actual pp277–280, equation1.1 and Theorem1.3
with proof, gives the precise row-flagged determinant/tableau identity.
Kumar, arXiv:2306.10289v1 (17 June2023), actual definitions, Theorem4,
its proof and Demazure specialization, uses complete root-of-unity tuples
and divisible flags. Our missing real letter in each cube-root triple
violates the h-degree vanishing used there. The d=2 theorem uses opposite
letters, not the two primitive cube roots. This is a bounded direct-applicability
comparison, not comprehensive classical-subsumption clearance.

Before significant calculation I screened the permitted complete registry
receipts in sol-fresh-analysis-discovery-r7, dated 2026-10-29 04:39–04:43 UTC:
trureturing67b4fae085cf19003a33f8027410c383b49e5046,
count-ex-machina dbf673741a54c7dc9d88a6aec0e8148a538f4a3a,
openai/math7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a.
Problems/D5/preprints trees are untruncated. I read the actual sibling
OhScrimshaw two-shifted refutation body: it explicitly excludes positivity.
Current public search located the indexed literal MathDB339078 statement;
its open status is not novelty evidence. No new GitHub API traversal and no
request to the previously403 MathDB route were made. No exhaustive live
solutions-body or journal clearance is asserted.

## The stronger claim under test

For r=2k let omega^2+omega+1=0, omega!=1. Define

 P_(n,r)(a_0,...,a_(r-1))
   = S_((n^r),(2,4,...,2r))
       (omega a_0,omega^2 a_0,...,omega a_(r-1),omega^2 a_(r-1)).

Equivalently, by Wachs,
P=det(H_(n-i+j)^(i+1))_(0<=i,j<r), where
sum_(d>=0)H_d^(m)z^d=product_(l=0)^(m-1)(1+a_l z+a_l^2 z^2)^(-1),
and H_d=0 for d<0. This definition is over Z[a], since each complete pair
has the displayed integral generating series.

The verified predecessor bridge gives, for t=q^(-1),

 Delta_n^r(q)=q^E t^binom(r,3) P_(n,r)(1,t,...,t^(r-1)),
 E=sum_(i=0)^(n-1)i^2+sum_(j=0)^(r-1)binom(n+j,2).

Thus independent-pair coefficient positivity would suffice for A.4, but the
converse need not hold: profiles with the same sum l*e_l coalesce.
This is not simply the previous independent-Motzkin-height hypothesis.
For arbitrary arrival weights b_h, normalized orthogonal polynomials obey
f_(h+1)=(x/b_h-1)f_h-f_(h-1). The prefix-product coefficient extraction
above used geometric b_h=q^h and its q-difference equation; replacing its
pair variables independently is a different extension. No equality between
the two arbitrary-weight extensions is assumed or proved here. Both specialize
to the literal geometric source, through their respective established bridges.

## Exact full pair-content counterexample

For n=3,r=6 (k=3),

 [a_0^3 a_1^5 a_2^2 a_3^5 a_4^2 a_5] P_(3,6) = -1.             (*)

Here is an ordinary finite proof encompassing ALL tableaux with this content.
For each l=1,...,6 let mu_l be the cells filled by letters at most2l.
Each mu_l is a partition inside (3^6); flags force its first l rows full.
The profile in(*) forces cumulative sizes3,8,10,15,17,18. Successive layers
have at most two cells per column since each uses only two letters.

Consequently mu_1=(3,0,0,0,0,0). At size8, the top two rows are full,
and the remaining2 cells can only form a row of length2: choosing(1,1)
would put three new cells in column1 of layer2. Thus
mu_2=(3,3,2,0,0,0). Size10 and the third full row force
mu_3=(3,3,3,1,0,0). At size15 and four full rows the remaining3 cells
are either(3,0) or(2,1). Finally sizes17,18 force
mu_5=(3,3,3,3,3,2), mu_6=(3,3,3,3,3,3).
These exhaust the TWO feasible chains; both have valid binary-layer fillings.

For a binary skew layer, let V count its double columns, and let L_i count
its remaining single cells in row i. Double columns force an upper1 and a
lower2. In a skew partition, forced upper1s lie left of the free upper cells,
and forced lower2s lie right of the free lower cells. Thus the remaining
weak binary row strings are independent, giving
s_(nu/mu)(x,y)=(xy)^V product_i h_(L_i)(x,y).
At x=omega a,y=omega^2 a, xy=a^2, and
h_L(omega a,omega^2 a)=a^L f(L), with f(L)=1,-1,0 for L=0,1,2 mod3.
This follows from (1+az+a^2z^2)^(-1)=(1-az)/(1-a^3z^3).
Different layers compare automatically, so their factors multiply.

For mu_4=(3,3,3,3,3,0), the six lists of NONZERO free lengths are
(3),(1),(1,1),(1),(2),(1). Layer5 has factor0; the whole chain contributes0.
For mu_4=(3,3,3,3,2,1), they are
(3),(1),(1,1),(1),(1,1),(1).
The corresponding signs are +,-,+,-,+,-, with product -1.
The double-column counts are0,2,0,2,0,0 for each chain, so the degrees
are exactly3,5,2,5,2,1. Summing the two exhaustive chains proves(*).
No sampled numerical values enter this proof.

Independent direct binary-tableau enumeration gives residue counts
(128,128,128) and(170,171,171), total(298,299,299), so the coefficient is
298+299omega+299omega^2=-1. Independently expanding the entire flagged
determinant at this content gives only three nonzero permutation terms:
zero-based permutations(0,2,1,3,4,5),(0,2,1,4,3,5),(0,2,1,5,3,4)
contribute respectively1,-3,1. These are redundant exact validations.

## Meaning and remaining gap

This counterexample disproves positivity even after summing all pair-position
classes having fixed content. It rules out a positive decomposition or
cancellation mechanism that preserves every pair's total count and seeks
positivity separately in each such component. It does not exclude cancellation
that changes contents while preserving geometric degree, or other positive
networks/characters for the specialized determinant.

The negative monomial specializes to -t^37. As an additional local diagnostic,
the full coefficient [t^37]P_(3,6)(1,t,...,t^5) is29, after summing different
contents. Thus the exhibited coefficient is explicitly repaired in the source
specialization. This calculation is not used as proof of any all-order claim.
The earlier n4r6 profile(4,7,4,6,2,1) with coefficient0 is unaffected.

Strongest objection: (*) is only a method obstruction. It earns zero discovery
credit and does not resolve or refute literal A.4. The exact remaining gap is
nonnegativity after aggregation over ALL contents of the same geometric degree
for every n and every even r, or a negative coefficient of a literal source
determinant. No uniform cancellation or eligible full result was obtained.
No PROOF.md, Lean development, paper or acceptance request is justified.

## Reproduction

Run `python check.py` and `python witness.py` in this directory.
The former tests modest full-content polynomials and stops at the first failure;
the latter independently enumerates all compatible tableaux at the single
witness content and expands its full determinant coefficient. Both impose
512MiB address space, CPU deadlines (55s/50s), and BLAS/OMP/MKL/NumExpr1
before calculation. All completed in under one second; no limits were raised.
Outputs: checks.json, witness.json. witness-extended.json additionally records
free-length data and the one geometric-degree aggregate; its calculation is
also reproduced by witness.py. No large target positivity grid was run.
