# H013 algebra review: conditional costs, not broad exclusions

2026-10-08. Claude Opus proposal retained in H013-algebra-opus-raw.md. Independent
native Astra checked shared-table/orbit costs; native Sol checked small-root
sources and collector accounting. Root checked the algebra, strengthened the
multi-output pair screen, and read the APS primary post-print. No experiment,
engine or Lean theorem. Verified improvement NONE.

## Shared-table baseline and scalar-orbit encoding

For B^m~q, constant useful yield and Theta(B) required rows, a FULL integer-split
table costs B^ell+B^(m-ell+1). Optimizing integer ell gives B^((m+1)/2) for oddm
but B^(m/2+1) for evenm. In particular m5,ell3 gives B^3 work and table entries.
The raw report incorrectly used a fractional ell under the constant-yield claim.

A different conditional construction for m=2k restricts one coordinate of a
(k+1)-sum table to B^(1/2) values. Table work/storage B^(k+1/2), right scan
B^(k-1) per query, presumed useful yield B^(-1/2), and B^(3/2) queries for B rows
recover B^((m+1)/2). Coverage/rank/log overhead remain assumptions. This is not
a unconditional generic ECDLP upper bound, much less a lower bound.

LO-PKM keeps U chosen signed base representatives w with unknown logs lambda_w,
then admits known scalar multiples [c]w for0<=c<D=2^n via projective bit ladders
and S3 chains. A verified decomposition of aG+bQ gives
sum epsilon_i*c_i*lambda_(w_i)-b*d=a modq. Combine repeated bases first.
Domain cardinality, rational liftable abscissae and independent unknowns differ;
including +/-w twice introduces dependencies. Expanded nonzero union has at most
U(D-1) points, often fewer because of overlaps. Multiplicity is not yield/rank.
Nonzero final projective Z excludes c0; shorter-arity charts or nonzero c must be
specified. Ladder initialization/infinity handling must preserve completeness;
final group verification alone does not repair excluded valid witnesses.

If F~UD is actual usable union size, only roughly U unknowns are being eliminated.
Its shared-table comparison is F^ell+U F^(m-ell), not F^ell+F F^(m-ell).
For m5, a fraction f=sqrt(U/F) of the3-sum table with right scan F^2 and useful
yield f gives setup fF^3 and (U/f)*F^2 query work, each sqrt(Uq). Again this
depends on useful yield/rank. It still exceeds square-root for growing U.

Under the separate HYPOTHETICAL decomposition cost C_dec=C_PKM(U)*D^(m/2),
constant useful yield, adequate rank and (UD)^m~q, the collection term equals

    U*C_dec = sqrt(q)*C_PKM(U)*U^(1-m/2).

This term improves only if C_PKM(U)=o(U^(m/2-1)). No operation achieving the
hypothetical factorization was supplied. It is not a lower bound or proof all
variable splits require generic lists. Fixed U does not prohibit coordinate
methods. Finite observed cost growth would not kill every such method.
Domain/circuit setup, empty queries, extraction, rank losses, verification and
memory remain paid; an O(U^2) sparse-work estimate does not require dense U^2
storage automatically. No executable search primitive to benchmark yet.

## CSR: remove the unsupported general rejection

The raw beta<=1/(m*2^(m-1)) polytope threshold was an uncomputed estimate.
Native Sol read [Jochemsz--May §2](https://www.iacr.org/archive/asiacrypt2006/42840270/42840270.pdf):
its norm/determinant conditions are sufficient, and extraction retains a nonzero-
resultant assumption. Failing a sufficient bound does not imply lattice
impossibility. The current official2024/1330 landing page identifies a revised
five-author paper; PDF returned403. No unread theorem supplies the raw rejection.
Per-query polylog(p) cost is unproved without bounding dimensions, shift levels,
coefficient sizes, extraction/output costs and failures. General m>=3 CSR is
undecided here. H012's particular t2 S6 screen does not settle all schedules.

There IS a cheap exact m2 collector bound. Freeze a signed B-point base and one
affine label pair for each conditionally uniform fresh R. Let D(R) count allowed
unordered pair decompositions; across all R there are at most B(B+1)/2 pairs.
Thus E[D(R)|past]<=B(B+1)/(2q). Each pair supplies at most one geometric row for
that query. Even with many outputs, predictable stopped-work accounting gives

    E[emitted rows] <= B(B+1)/(2q) * E[queries].

If this collector succeeds with constant probability only after >=cB output
rows, it needs Omega(q/B) queries. Paid emission also costs Omega(B); total is
Omega(max(B,q/B))>=Omega(sqrt q). Duplicates/linear combinations do not count as
new geometric rows. This is a bound on a FIXED-BASE, UNIFORM-TARGET collector
with that row requirement, not every two-point recovery strategy. Root proposed
the multi-output refinement and Sol independently confirmed it.

A separately frozen S4 level-one module also fails its chosen certificate:
centered monic F=S4(X1,X2,X3,r) has unique degree12 term l=X1^4 X2^4 X3^4.
Generate the integer module by F and pX^alpha for OTHER monomials of suppF.
Then g=cF+ph has l coefficient c. If c!=0 its box-scaled Euclidean norm is
>=B^12; otherwise nonzero g has norm>=p. When B^12>=p, none passes the strict
sufficient norm threshold p/sqrt(number of terms). This excludes only that
level/shift/certificate schedule, not more shifts or other recovery. It supplies
no reason to build a lattice engine around the broad uninstantiated CSR card.

## Source checks and transfer limitations

Root read [Amadori--Pintore--Sala post-print](https://iris.unitn.it/handle/11572/202653),
§§3–3.3, both via publisher-hosted PDF and delegate's local text. It builds
random affine-labelled base points and seeks one useful zero-sum relation. It
explicitly leaves polynomial-solving cost unestimated and does not claim to beat
square-root algorithms. Its comparison to PKM assumes comparable solver costs;
do not turn the abstract's improvement wording into a proven ECDLP speedup.
Known-label bases remove a row-collection requirement only by replacing it with
a paid useful-dependency search. Earlier collector bounds were deliberately scoped.

GLUE supplies no subgroup-sensitive faster backend. Root checked Diem's primary
[abstract](https://arxiv.org/abs/math/0606607): fixed-genus expected bound
tildeO(p^(2-2/g)) assumes a bounded-degree plane model and CYCLIC class group.
Those hypotheses are not automatically proved for a proposed glued Jacobian.
The advertised cost bound is not below sqrt(q) for q~p,g>=2; it is an UPPER
bound, not a lower bound on every transfer algorithm. Gluing construction and
root extraction also need paid specification. No broad genus/transfer rejection.
The eprint2004/153 PDF returned403; no theorem attributed to an unread file.

Other raw bridge dismissals (sparse root detection, fast products, isogenies,
large automorphism orbits) do not establish universal exclusions. A field-map
degree or generic hardness assertion is insufficient. Retain as source leads
and missing operations only. No verified improvement, no new numerical result.
