# r144: zero nominees

The strongest investigated lead was Rosas-Ribeiro–Bras-Amorós,
*Infinite chains in the tree of numerical semigroups*, Semigroup Forum
110 (2025), 229–248, DOI 10.1007/s00233-024-10487-x, Conjecture 6.1.
This lane does not resolve that target and does not nominate its reductions,
finite controls, onset issue, or any parameter case as a discovery.

## Source and scope

For every fixed integer multiplicity m>=2, let i_g(m) count numerical
semigroups of multiplicity m and genus g that lie on an infinite chain in
the parent tree. The claim is existence of a period P_m>=1 and rational
polynomials Q_{m,0},...,Q_{m,P_m-1} such that

    i_g(m)=Q_{m,g mod P_m}(g) for EVERY integer g>=m-1.

The displayed formulation is the substantive m>=2 target investigated here.
The source sentence itself says fixed multiplicity m without an explicit
m>=2 qualification. The degenerate m=1 range is not used to manufacture
a domain/onset correction or a discovery. No full source resolution is claimed.
The period is allowed to depend on m. Eventual equality is strictly weaker.
No degree or period bound is imposed by the question. A finite failure of
an arbitrarily guessed period is not a refutation.

Latest arXiv abstract history identifies v2, 14 November 2024; the retained
unversioned HTML and explicit v2 bytes coincide. Actual v2 Section 6 and
the updated publisher Section 6 give the same quantifiers. The publisher's
17 January 2025 correction, read in full, fixes an abstract citation, not
Conjecture 6.1. The main primary body supplies Theorem 3.4(a), the gcd
criterion, Corollary 4.1 and its proof, and the prime/4/6 special formulas.
The companion 2401.18060 proves rarity across all semigroups as genus grows;
that different asymptotic does not imply the fixed-multiplicity assertion.

## Early collision screening and limits

The retained r141 index was reused, with hashes refreshed and new original
SUMMARY/discovery/PROOF/review/DECISION-role paths added. 1,710 original-role
bodies were searched in full, with no match-count cutoff. Nine paths changed
relative to the retained baseline. Original r111–r113 science remains in
the inherited qualified records; generated extraction/context echoes were
not added as new science. Exact title, authors, DOI and arXiv ID searches
had no matches. Broad numeric searches had false positives in hashes,
byte ranges and constants; these are not scientific collisions. Matching
original bodies were reopened and their exact matching contents retained
under sources/history-HASH.txt. See alias-queries.jsonl.
The selected target was screened before retrieval. For Kaplan's comparator
and the correction DOI, dedicated exact-title/DOI screens were completed
retrospectively: the earlier prefetch screen covered the general Kunz and
semigroup-quasipolynomial aliases, not both exact comparator identifiers.
This sequencing limitation is retained; no complete compliance claim is made.

An earlier power-monoid pool was abandoned: public 2608.27292v2 explicitly
discusses the Tringali–Yan resolution, with a July 2026 antecedent, and
the 2512.12606 latest abstract distinguishes finitary from reduced power
monoids. No conclusion about an old open label was used as clearance.
The Lie-superalgebra lead was stopped at the first HTTP429; no bypass.

## Actual mathematics: Apéry top-band reduction

Use standard Kunz coordinates x_1,...,x_{m-1}>=1 and w_i=m*x_i+i.
The operative classical conditions (Kaplan Propositions 4–5) are

    x_i+x_j >= x_{i+j}                 if i+j<m,
    x_i+x_j+1 >= x_{i+j-m}             if i+j>m.

The omitted i+j=m conditions are automatic. Then genus=sum x_i and
conductor c=max_i(w_i)-m+1. For a divisor d>1 of m, ALL positive left
elements are divisible by d if and only if

    w_i >= c for every i not divisible by d.                 (A)

Indeed w_i is the first semigroup element in residue i mod m; d divides m,
so every element of that residue has its same residue mod d. This proves
both directions, including the empty-left-set ordinary semigroup. For a
nonordinary semigroup the left gcd divides m, since m<c. The source gcd
criterion is therefore equivalent to the union of (A) over primes dividing
m; ordinary semigroups satisfy every (A). Inclusion–exclusion uses the
nonempty squarefree divisors of m, with coefficient (-1)^(omega(d)+1).

Choose the unique j with w_j=max w_i. Each j-case is a finite system of
linear inequalities: w_i<=w_j for all i, and w_i>=w_j-m+1 for i not
divisible by d. There are no ties because the residues are distinct.
Together with Kunz and sum x_i=g these are bounded rational polytopes
whose inequalities depend affinely on g. Kaplan's actual Theorem 8
(Chen–Li–Sam's generalized Ehrhart theorem) implies EVENTUAL
quasipolynomiality for each case; a finite sum does likewise. This is a
routine application of that classical theorem, not a nominated result.

A more compressed parametrization exposes what the reduction does and
does not settle. Write w_j=m*M+j. For every nonmultiple i of d, (A) and
maximality force

    x_i=M if i<=j, and x_i=M-1 if i>j.

Only the coordinates x_{dk}, 1<=k<m/d, remain free. Their internal Kunz
inequalities are exactly those of multiplicity m/d; mixed residue
inequalities still require care at small M. The fixed-genus equation is

    g=(m-m/d)*(M-1)+#{i<=j : d does not divide i}+sum_k x_{dk}.

This compression suggests degree at most m/d-1 but is not used here to
claim a sharp degree, leading coefficient, onset, or exact generating
function. In particular no all-m Ehrhart dilation without offsets was found.

There is also a direct quotient control. If c>m and (A) holds, set
n=ceil(c/d) and T={t<n:dt belongs to S} union [n,infinity).
Then T is a numerical semigroup of multiplicity m/d, with conductor<=n,
and, writing h for its genus,

    g=c-n+h,
    S={dt: t in T, dt<c} union [c,infinity).

Closure of T follows by scaling sums below n; all larger sums lie in
its appended tail. The genus identity counts the n-h nongaps below c.
For a converse parametrization one must ALSO require c-1 absent from S;
when c=1 mod d this is a genuine condition on the last quotient position.
Ignoring this condition would double-count conductors. No such converse
shortcut is asserted.

## A concrete failed proof route

Uniformly subtracting 1 from every Kunz coordinate preserves the band
differences, but need not preserve closure. At m=8 take

    x=(6,2,6,4,6,6,6), g=36, c=48.

All Kunz inequalities hold and every odd-residue w_i is at least 48,
so the source gcd criterion applies. After subtraction,
x'=(5,1,5,3,5,5,5), but 2*x'_2=2 < x'_4=3. Thus an argument claiming
that every sufficiently non-boundary top-band point retracts by uniform
translation is false. This witness is a method obstruction, not a
counterexample to Conjecture 6.1 and not a new credited result.

## Exact checks and their falsifiers

checks.py uses integer arithmetic only, bounded by the unchanged helper
guard. It explores the infinite-chain tree for m=2,3,4,5,6,7,8,9,10,12
through genus40: 11,340 states. All 2,861 quotient reconstruction checks,
top-band/gcd/inclusion–exclusion controls, and the source prime/4/6
formulas pass. No state cap was reached. Independently, all 9,907 positive
compositions at m=2..8, g<=14 were screened with the Kunz inequalities;
their resulting counts agree with the tree counts in 77 cases. The
translation obstruction above also passes. These finite checks do not
prove quasipolynomiality, its onset or public priority.

An exact falsifier of (A) would be a valid Kunz tuple for which the
divisibility of actual left elements disagrees with the displayed band
condition. A falsifier of the quotient identity would be an eligible S,d
with failed reconstruction or g != c-ceil(c/d)+h. A full source refutation
instead needs an exact eventual quasipolynomial forced on ALL sufficiently
large g in some multiplicity, plus an incompatible value in the source
range; a finite interpolation alone cannot provide it.

## Public overlap and remaining gap

A later exact-title/claim-alias search located Zhanhe Zhang's SSRN7566078,
*Quasipolynomial Counts of Numerical Semigroups in Infinite Chains at Fixed
Multiplicity*, date written 5 October2026, posted7 October2026. The indexed
primary abstract asserts precisely an m=8 onset defect, period1638, and
the general eventual theorem with degree m/p(m)-1. Both SSRN landing and
delivery bodies returned HTTP403 through public web retrieval. No bypass,
repeated shell retry, full proof-body read or independent validation of
that claimed refutation is asserted. The exact overlapping PUBLIC CLAIM
is enough to stop discovery investment; it is not reported as a verified
public proof. Reconstructing that announced result would not be fresh.

Our own remaining mathematical gap is a full proof/refutation of the
all-g source target; the strongest attempted proof only yields a classical
eventual statement. The strongest eligibility objection is the exact
earlier public overlap, independently of the excluded routine partial
reduction and the user's exclusion of domain/onset corrections. No Lean,
manuscript or PROOF.md is produced.

The cached registry paths and bounded returned deltas do not clear theorem
bodies: aa026->a19a and a19a->490f both have300-path caps. r140's three
Markdown reads cover only their named scopes. OpenAI7ef5 is inherited as
unchanged, not newly checked here. No current head chasing or blanket
semantic registry clearance was performed. No worldwide-priority claim.
