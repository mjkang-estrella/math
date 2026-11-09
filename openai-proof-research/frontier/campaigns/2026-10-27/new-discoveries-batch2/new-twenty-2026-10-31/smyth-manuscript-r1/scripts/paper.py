from pathlib import Path
import subprocess,re
R=Path(__file__).resolve().parent.parent
s=r'''.char \[dom] \h'1p'\D'l 0 -6p'\D'l 6p 3p'\D'l -6p 3p'\v'2p'\D'l 6p 0'\v'-2p'\h'2p'
.char \[domleft] \h'7p'\v'-6p'\D'l 0 6p'\D'l -6p -3p'\D'l 6p -3p'\v'8p'\D'l -6p 0'\v'-2p'\h'8p'
.EQ
delim $$
.EN
.nr PS 11
.nr VS 14
.nr PO 0.85i
.nr LL 6.8i
.nr LT 6.8i
.nr HM 0.65i
.nr FM 0.55i
.ds CH Smyth injection counterexample | DRAFT
.ds CF \\n[PN]
.de H
.sp .4
.B \\$1
.sp .2
..
.TL
A down-set counterexample to Smyth's
injection conjecture on compositions
.AU
AI-assisted research draft | MathDB 332037
.AI
Prepared with OpenAI Codex; no human authorship or affiliation asserted
.PP
DRAFT, 4 November 2026. This document is an unpublished, AI-assisted manuscript
for human review. It claims no priority and no accepted campaign credit.
Its mathematical conclusion is a finite refutation of Conjecture 1.5 of
Smyth [1]; the related probabilistic and total-nonnegativity theorems are
not refuted. The significance is modest: the conjecture is low-profile and
not needed for the source's established theorems.
.H "1. Source statement and conventions"
.PP
Throughout, N denotes the non-negative integers. Put [m] = {1,...,m}, with
[0] empty. Smyth's set U^m consists of maps from [m] to N; these are ordered
compositions with m non-negative parts, so zero parts are allowed. Write
|lambda| for the sum of the coordinates and U^m_n for the maps of weight n.
The empty map has weight zero. A partition is a non-increasing sequence
of non-negative integers with finite support. Finite partitions are padded
with zeros when necessary.
.PP
Write lambda_p for the non-increasing rearrangement of lambda. For partitions,
mu dominates lambda, written mu \[dom] lambda (equivalently lambda \[domleft] mu),
when their weights agree and each initial sum of mu is at least the
corresponding initial sum of lambda. Thus
.EQ
mu ~ "dominates" ~ lambda ~ iff ~ | mu | = | lambda | ~~ "and" ~~
sum from {i=1} to j mu(i) >= sum from {i=1} to j lambda(i) ~~ (j >= 1).
.EN
.PP
For compositions, dominance means dominance of their rearrangements.
Concatenation lambda mu places the A coordinates of lambda first and the B
coordinates of mu second; its length is A+B and its weight is a+b when the
weights are a and b. Permuting coordinates preserves this dominance relation.
.H "Conjecture 1.5 [1] (verbatim)"
.QP
For all integer $A,a,B,b$ with $A >= B >= 0$ and $a >= b >= 0$ there is an
injection
.EQ
 gamma : U sub b sup A times U sub a sup B ~ "\(->" ~ U sub a sup A times U sub b sup B
.EN
.QP
such that for all $(lambda sub 1 , mu sub 1 ) ~ member ~ U sub b sup A times U sub a sup B$,
$(lambda sub 2 , mu sub 2 ) = gamma ((lambda sub 1 , mu sub 1 )) ~ member ~ U sub a sup A times U sub b sup B$
satisfies $lambda sub 1 mu sub 1$ \[dom] $lambda sub 2 mu sub 2$.
.PP
The source's dominance symbol means that the domain concatenation dominates
its image. The injection arrow above is printed as an ordinary arrow;
its injectivity is asserted in the quoted sentence. The original TeX, PDF,
and exact MathDB raw line are included in the dossier.
.bp
.H "2. An explicit down-set obstruction"
.PP
Theorem. For (A,a,B,b) = (3,20,2,19), the injection in Conjecture 1.5 does
not exist. Consequently its universally quantified assertion is false.
.PP
Let G consist of the following eight non-increasing partitions, each of
weight 39:
.DS L
(13,12,8,4,2)     (13,13,7,3,3)
(12,12,8,6,1)     (14,12,6,4,3)
(13,11,7,7,1)     (14,11,6,6,2)
(15,11,5,5,3)     (16,10,5,4,4).
.DE
.PP
Let D be the down-set of partitions of 39 dominated by at least one member
of G. This definition allows partitions of arbitrary finite support.
Only its intersection with partitions having at most five parts is used
in the counts below. Set
.EQ
X = U sub 19 sup 3 times U sub 20 sup 2 , ~~
Y = U sub 20 sup 3 times U sub 19 sup 2 .
.EN
.PP
For a pair x = (lambda,mu), put r(x) = (lambda mu)_p, and define
S = {x in X : r(x) in D} and T = {y in Y : r(y) in D}.
Literal enumeration gives
.EQ
|X| = 210 cdot 21 = 4410 , ~~ |Y| = 231 cdot 20 = 4620 ,
.EN
.EQ
|S| = 1137 , ~~ |T| = 1134 .
.EN
.PP
These are counts of ordered pairs, including all zero coordinates, not
counts of partitions. One can reproduce them without an optimization
solver: enumerate the first two coordinates of each three-part composition,
force the third by the weight, enumerate the first coordinate of each
two-part composition, force its second, then sort all five entries and
compare their initial sums against every generator. See Section 3.
.H "Proof of the theorem"
.PP
Assume that an injection gamma as conjectured exists at these parameters.
Take x in S. By definition some g in G dominates r(x). The conjecture says
that r(x) dominates r(gamma(x)). Dominance is transitive: total-sum
equalities compose, and each pair of corresponding initial-sum inequalities
composes. Hence g dominates r(gamma(x)), so gamma(x) is in T.
Therefore gamma restricts to an injection from S to T. Finite injectivity
would give |S| at most |T|, contradicting 1137 > 1134. This proves the
parameter refutation and thus the negation of the universal conjecture.
.PP
No maximum-matching assertion is needed for this proof. Nor is it necessary
to enumerate the entire down-set among partitions of unrestricted length:
all domain and image concatenations here have exactly five coordinates.
.bp
.H "3. Reproducing the finite certificate"
.PP
The fresh standard-library script scripts/audit.py defines compositions
recursively from their length and weight. At length zero it returns the
empty tuple only for weight zero. At positive length it loops over the
first entry from zero through the weight and recursively enumerates the
remaining weight. Induction on the length shows that this returns every
composition exactly once. Rearrangement is decreasing sorting. The dominance
predicate checks equality of total weights followed by all initial sums,
with zeros beyond either tuple's length.
.PP
For a direct hand-oriented decomposition, group each filtered pair by the
first coordinate i of its three-part composition. The S row uses sums
19-i and 20 in the remaining two-part compositions; the T row uses 20-i
and 19. The resulting row counts are:
.TS
center;
r r r.
i	S row	T row
0	0	0
1	45	36
2	78	68
3	109	96
4	128	120
5	127	128
6	128	120
7	119	120
8	106	108
9	93	96
10	80	84
11	65	72
12	42	58
13	17	28
.TE
.PP
Every remaining S row, through i = 19, and T row, through i = 20, is zero.
Summing the columns gives 1137 and 1134. The dossier contains the complete
lexicographically ordered pair lists S.json and T.json, encoded as JSON
arrays of pairs of integer arrays. Their SHA-256 values are recorded in
audit-certificate.json and PROOF.md; they agree with the frozen discovery
and independent-review lists. The intersection of D with the five-part
partition universe has 262 members, an additional diagnostic count.
.PP
All mathematical cardinalities printed in this draft were independently
recomputed by a fresh isolated Python audit. The numeric-claim ledger
separates direct enumeration, supporting flow computations, mathematical
proofs, and bibliographic or module identifiers. Enumeration and Python
are reproducibility aids; the supplied Lean certificate checks the central
counts in the kernel. The manuscript lane did not execute Lean.
.bp
.H "4. Supporting computations and true special cases"
.PP
The fresh audit obtains a maximum admissible matching of 4407 out of
4410 domain elements at the counterexample parameters. The frozen review
reports the same value from element-level Hopcroft-Karp and a type-level
maximum flow; this dossier also recomputes those values. Reversing the
dominance orientation gives maximum matching 4050. This is a diagnostic
against a possible reading error, not the conjecture being refuted.
.PP
The flow groups elements by their sorted concatenation and retains their
multiplicities. A type network may use directed unit balancing transfers:
move one unit from a coordinate at least two larger than another, then
sort again. Such transfers generate dominance among fixed-length integer
partitions. With capacities equal to type multiplicities at the source
and sink and large intermediate capacities, integral flow equals admissible
matching. The audit checks the multiplicity formula against literal
ordered enumeration at the counterexample parameters.
.PP
Supporting computation finds no failures for A,B,a,b at most 10 with
A at least B, a at least b, and a+b at most 16. The nontrivial region
A > B at least 2 and a > b is checked by exact flow; the remaining
cases follow from the constructions below or empty-domain cases.
For (A,a,B,b) = (3,b+1,2,b), failures occur at every tested b from 19
through 43. This is a finite observation, not an infinite-family theorem,
and neither sweep contributes separate credit.
.H "Explicit constructions"
.PP
When A = B, send (lambda,mu) to (mu,lambda). This is injective, and the
concatenations have identical rearrangements. When a = b, use the identity.
When B = 1, write mu = (a), put delta = a-b, and send
(lambda,(a)) to (lambda+delta e_1,(b)). The first coordinate recovers lambda
by subtracting delta; all other coordinates are unchanged, so the map is
injective and has the required target weights.
.PP
To check dominance for this last map, write t = lambda(1), so 0 at most t
at most b at most a. The two-coordinate vector (t,a) has the same sum as
(t+delta,b), and each target coordinate is at most a. It therefore
majorizes that target pair. Appending the unchanged coordinates preserves
majorization: the sum of the largest j entries of an appended vector is
the maximum, over the number chosen from each block, of the corresponding
largest-entry sums in those blocks. Thus the required inequalities persist.
.PP
When B = 0, the domain is empty unless a = 0, which also forces b = 0;
then both sides consist of their zero maps. This covers A = 0 as well.
These constructions prove special cases for all their allowed parameters;
they do not suggest that an untested range has been exhausted.
.bp
.H "5. Formal correspondence and trust boundaries"
.PP
The reused source-only Lean ZIP has SHA-256
.DS L
\s[8]82e134f245cd795d51695f1a1be8a15b4167212ff4742d18f2a2f0c5ce7ac0c2\s0
.DE
.PP
It is copied byte-identically, not regenerated. The endpoint is
Smyth1512.not_conjecture15 : not Smyth1512.Conjecture15.
The statement quantifies over all natural A,a,B,b with B at most A and
b at most a. It uses exactly the source domain and target.
.PP
Base.lean defines U as the sum-n subtype of functions Fin m to N. Adding
one to the Fin index identifies it with [m], including the empty case.
The rearrangement is insertion sorting of List.ofFn in non-increasing
order. DomL asserts sum equality and every prefix inequality; Dom applies
it to rearrangements. concat is Fin.append. The seven statement definitions
U, rearr, psum, DomL, Dom, concat and Conjecture15 are textually identical
to the discovery draft judged faithful by the independent review. This is
checked as text, separately from checking the formal proof.
.PP
Bridges.lean proves completeness and absence of duplicates of the structural
composition enumerator; the Boolean dominance test agrees with all-prefix
dominance for five-entry lists. Prefixes beyond the length equal the total
sum. It also proves transitivity, concatenation correspondence, and list-to-
function realization with sum and List.ofFn round trips.
.PP
CountBase.lean decomposes the filtered enumeration by its first coordinate.
The S and T row modules prove the proposed row numerals by kernel decision;
Counts.lean adds them to obtain the two cardinalities. Endpoint.lean turns
an assumed conjectured injection into an injection on the finite filtered
lists and applies the cardinality inequality. Controls.lean proves that
rearrangement is sorted and a permutation, and provides a nonempty true
identity instance at A = B = a = b = 1. This is a control on the definitions,
not a replacement for their source correspondence.
.PP
The packet has 48 Lean modules. The frozen formalization report records a
fresh extracted strict compilation of all modules and an explicit-module
leanchecker pass for each. Its audit prints only propext, Classical.choice
and Quot.sound for the endpoint, and flags no unsafe or partial declarations,
implementation substitutions, extern declarations, or added axioms in the
local namespace. Mathematical source scans exclude sorry, admit and
native_decide. The dossier preserves the logs and known development
failures rather than presenting only successful runs.
.PP
These are supplied replay results, not a replay performed by this manuscript
worker. Lean, lake and leanchecker were not run here. The dependency pin is
Lean 4.34.1 and mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612.
Safe extraction was tested without execution. Root's final replay and live
registry refresh are STATUS_PARENT. The root replay reports success for every packet module and its checker.
The refreshed registry result is a path screen with selected header reads,
not an exhaustive proof-body search. Human review of statement fidelity,
the trusted toolchain and libraries, and bounded prior-art evidence remain
separate from the kernel's arithmetic and logical checks.
.bp
.H "6. Motivation, retention and related work"
.PP
Smyth's motivation is a combinatorial route to total nonnegativity. For a
non-negative TN_2 sequence p, let p_lambda be the product of its entries at
the coordinates of lambda. Lemma 2.1(iii) of [1] says that lambda dominating
mu implies p_lambda at most p_mu. Theorem 3.1 explains how the proposed
injection would therefore give
.EQ
(p sup A ) sub b (p sup B ) sub a <= (p sup A ) sub a (p sup B ) sub b ,
.EN
.PP
where (p^i)_j denotes the coefficient of x^j in p(x)^i. Nonnegative
unmatched target terms make summing legitimate. This would imply the
k = 2 case of the source's Theorem 1.4 about its coefficient matrix.
That theorem is proved independently in the source. Theorem 3.1's
intermediate reversed product inequality is a typographical error: the
lemma and the final comparison give the stated orientation. The submitted
Order manuscript [2] corrects that sign and states the implication as
Theorem 7, following Conjecture 6.
.PP
A down-set indicator weights tuples more freely than the product weights
p_lambda available from a TN_2 sequence. Hence the obstruction refutes the
proposed injection, not the product inequality or Smyth's probabilistic
characterization. It closes a particular proposed combinatorial route;
it does not undermine an established theorem.
.PP
The cached author publications page links [2] as the Order paper. That
submitted manuscript, created on 27 July 2016, retains the conjecture
verbatim as Conjecture 6, with unchanged quantifiers and orientation.
The review matches its abstract, keywords and reference list with the
published record [3]. This is positive retention evidence. The
post-refereeing printed body is UNREAD; neither this draft nor its dossier
claims direct verification of retention in that body. Root's ruling accepts
this as a qualified limitation for proceeding, not a novelty proof.
.PP
The supplied zbMATH review describes the main characterization and its
extension but does not discuss this conjecture. Readable citing material
examined in the review cites Smyth generically or concerns total positivity;
some other citing bodies were inaccessible or not read. Cached registry
path screens and bounded searches found no resolution. Such negative
search results do not prove priority, and no priority claim is made here.
The root must decide acceptance; this lane has zero accepted credit.
.H "References and provenance"
.IP "[1]" 3
Clifford Smyth. A Probabilistic Characterization of the Dominance Order on
Partitions. arXiv:1512.04084v1, 13 December 2015. The cached arXiv record
lists only this version. Source for Conjecture 1.5 and definitions.
.IP "[2]" 3
Clifford Smyth. Same title. Author-hosted submitted Order manuscript,
27 July 2016. Cached author-page link and download receipts in evidence/.
Conjecture 6 and Theorem 7. Not identified as the final printed body.
.IP "[3]" 3
Clifford Smyth. Same title. Order 35 (2018), 393-402.
DOI: 10.1007/s11083-017-9438-z (verified in the supplied publisher metadata).
Bibliographic record only; the printed body was not read.
'''
s=s.replace('STATUS_PARENT','reported complete in the supplied root receipts')
s=s.replace('lambda',r'\(*l')
s=s.replace(' member ',r' "\(mo" ')
s=s.replace('U^m_n','$U sub n sup m$').replace('U^m','$U sup m$')
(R/'paper.ms').write_text(s)
with (R/'paper.ps').open('wb') as f:
 subprocess.run(['groff','-e','-t','-Tps','macros.tmac','paper.ms'],cwd=R,stdout=f,check=True)
subprocess.run(['gs','-q','-dSAFER','-dBATCH','-dNOPAUSE','-sDEVICE=pdfwrite','-sOutputFile=paper.pdf','paper.ps'],cwd=R,check=True)
