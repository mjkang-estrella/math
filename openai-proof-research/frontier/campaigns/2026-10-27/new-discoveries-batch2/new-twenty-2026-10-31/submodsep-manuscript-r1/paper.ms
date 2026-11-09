.po 0.85i
.ll 6.8i
.nr PS 11
.nr VS 13
.nr HM 0.65i
.nr FM 0.55i
.ds CH DRAFT  |  MathDB 341850
.ds CF %
.EQ
delim $$
.EN
.EQ
define phi /"\(*f"/
define sigma /"\(*s"/
define cap /"\(ca"/
define cup /"\(cu"/
define in /"\(mo"/
define notin /"\(nm"/
define subset /"\(sb"/
define subseteq /"\(ib"/
.EN
.TL
A Four-Edge Obstruction to Submodular Separation
of Quadratic Boolean Monomial Images
.AU
Research draft prepared with OpenAI Codex assistance
.AI
No human authorship or institutional affiliation is asserted.
.AB
The low-degree Boolean monomial image at degree two in five variables cannot be the negative set of a submodular integer-valued function. This refutes Conjecture 3.33 in the read 2019 preprints of Brakensiek, Gopi and Guruswami, even after its efficient-evaluation requirement is removed. The shortest proof is an explicit four-edge dependency cycle, applying Elbracht-Kneip-Teegen. An independent symmetric certificate has thirteen rows and is the argument formalized by the supplied Lean development. We give both certificates and exact checks of smaller feasible cases. The 2022 journal version of record remains unread; retention of the conjecture there is not certified. This is a draft, with AI assistance, not an acceptance or priority determination.
.AE
.NH 1
Source setting and the conjecture
.ft R
.ps 11
.PP
For integers $0 <= r <= d$, index the output coordinates by all subsets $S$ of $[d]$ with $|S| <= r$, including the empty subset. Set
.EQ
n = sum from {k=0} to r { left ( pile {d above k} right ) }, ~~~
phi ( x ) = left ( prod from {i ~ in ~ S} x sub i right ) sub {S ~ subset ~ [d],~ |S| <= r}, ~~~
F sub {r,d} = phi ( "{" 0,1 "}" sup d ).
.EN
The empty product is one. Identify the Boolean cube with a subset lattice: meet is intersection (coordinatewise AND), and join is union (coordinatewise OR). Submodularity means
.EQ
f(A cap B) + f(A cup B) <= f(A) + f(B) ~~~ "for all" ~ A,B.
.EN
The image family is intersection-closed: intersecting input supports intersects their collections of contained low-degree labels.
.PP
Here is Conjecture 3.33 verbatim in mathematical typography from the read arXiv v1, printed page 23 [1]; the ECCC copy has the same text. The notation $F sub {r,d}$ denotes the family above.
.QP
Conjecture 3.33. For every $0 <= r <= d$ and $n = left ( pile {d above {<= r}} right )$, there exists a submodular function $f : "{" 0,1 "}" sup n -> bold Z$ such that:
.IP 1. 0.3i
$f(x)$ can be evaluated in $roman poly(n)$ time for every $x ~ in ~ "{" 0,1 "}" sup n$.
.IP 2. 0.3i
For all $x ~ in ~ F sub {r,d}$ (defined as above), $f(x) <= -1$ and for all $x ~ notin ~ F sub {r,d}$, $f(x) >= 0$.
.LP
The source asks whether the ETH-based hardness of HORN-SAT-MOD for non-prime-power moduli can be transferred to SUBMOD-MIN-MOD. Proposition 3.34 assumes this conjecture to replace Boolean feasibility by negativity of an efficiently evaluable submodular objective; Corollary 3.35 derives a conditional hardness bound. Our counterexample invalidates the universal separator premise of that proposed reduction. It does not decide the complexity of modular submodular minimization.
.ZF
.bp
.ZH
.NH 1
The shortest proof: a dependency cycle
.ft R
.ps 11
.PP
\fBTheorem.\fP There is no submodular function $f : "{" 0,1 "}" sup 16 -> bold Z$ satisfying $f <= -1$ on $F sub {2,5}$ and $f >= 0$ outside it. Consequently Conjecture 3.33 fails without its evaluation-time clause.
.PP
Work on the face where the empty-monomial coordinate is one. Label the other coordinates, in order, by
.EQ
0,~1,~2,~3,~4,~01,~02,~03,~04,~12,~13,~14,~23,~24,~34.
.EN
A label such as 01 denotes the pair $"{"0,1"}"$. A decimal mask $m$ encodes these fifteen bits, with the first coordinate the least significant bit. Write $q(X)$ for the mask of all singleton and pair labels contained in $X subseteq "{"0,1,2,3,4"}"$. The thirty-two good masks are exactly the monomial image on this face. A mask outside that image is bad. The restriction $h$ of $f$ remains submodular, since the face is a sublattice. Thus an obstruction here is an obstruction on the full cube.
.PP
Elbracht, Kneip and Teegen [2, Lemma 4.1 and Corollary 4.2] show that the dependency digraph of an order-induced submodular partial lattice is acyclic. In the outer-edge case used here, $a,b$ are bad, $c$ is good, and $b$ is one of $a cap c$ and $a cup c$ while the other point is bad. Submodularity forces strict decrease from $a$ to $b$; our signs give a decrease of at least one.
.PP
The independent review supplies the following four rows. All meets and joins are bitwise AND and OR.
.TS
center box;
r r r r r l.
a	b	good c	a AND c	a OR c	input X for c
_
103	5743	5646	6	5743	{1,2,3}
5743	1067	19899	1067	24575	{0,1,3,4}
1067	5359	4301	9	5359	{0,2,3}
5359	103	11127	103	16383	{0,1,2,4}
.TE
.PP
In each row $c=q(X)$. The starting points, endpoints, and the other meet/join points 6, 24575, 9, 16383 are bad: each fails the test that its pair bits are exactly all pairs of its singleton support. The four submodular inequalities give, respectively,
.EQ
h(5743) <= h(103) + h(5646) - h(6) <= h(103) - 1,
.EN
.EQ
h(1067) <= h(5743) + h(19899) - h(24575) <= h(5743) - 1,
.EN
.EQ
h(5359) <= h(1067) + h(4301) - h(9) <= h(1067) - 1,
.EN
.EQ
h(103) <= h(5359) + h(11127) - h(16383) <= h(5359) - 1.
.EN
Adding cancels every function value and yields $0 <= -4$, a contradiction. This is the shortest proof presented here; no graph-girth minimality claim is needed. It even rules out real-valued separators with these signs. This applies the published obstruction criterion; no new general obstruction is claimed.
.ZF
.bp
.ZH
.NH 1
An independent symmetric certificate
.ft R
.ps 11
.PP
The supplied Lean proof uses a different certificate. Sum over all permutations of the five input variables:
.EQ
g(m) = sum from {sigma ~ in ~ S sub 5} h( sigma ~ m ).
.EN
A permutation renames both singleton and pair labels. It preserves meet, join and the good family. Hence $g$ is submodular, constant on permutation orbits, at most $-120$ on good masks and nonnegative on bad ones. This is a sum, not a normalized average; no division is used.
.PP
For each row below let $R = g(u)+g(v)-g(a)-g(b)$, where $u=a~roman AND~b$ and $v=a~roman OR~b$. Then $R <= 0$. These are all nine submodular rows and their positive weights.
.TS
center box;
r r r r r.
a	b	u	v	weight
_
8191	15359	7167	16383	1
15327	3259	2203	16383	1
28957	1791	29	30719	1
518	15	6	527	1
518	47	6	559	1
5646	39	6	5679	1
5646	119	6	5759	1
5646	655	526	5775	1
32286	615	518	32383	2
.TE
.PP
Add four sign rows, with the weights already included:
.EQ
-4g(3) <= 0, ~~~ 5g(615) <= -600, ~~~
2g(5871) <= -240, ~~~ -3g(16383) <= 0.
.EN
Here $615=q("{"0,1,2"}")$ and $5871=q("{"0,1,2,3"}")$, whereas 3 and 16383 are bad. The sum of all thirteen weighted left sides vanishes identically for orbit-invariant $g$. Thus
.EQ
0 <= -600 - 240 = -840,
.EN
again a contradiction.
.PP
Check cancellation without trusting orbit labels or a numerical solver: expand every $g$ as its sum of $h$ values over all 120 permutations. The resulting integer coefficient of each actual mask is zero. Our fresh isolated Python verifier regenerates the coordinate action and good family from their definitions. It verifies all meet/join identities after renaming, all sign classifications, and every coefficient. There are 1,080 submodular row instances, touching 365 distinct masks across the complete certificate, and no residual coefficient. Total good-row weight seven gives the upper bound $-120 times 7 = -840$.
.PP
The weights are exact integers. The historical search used linear programming to locate and compress the obstruction, but no optimization oracle or floating-point assertion is a premise of either proof. Our fresh verification runs no solver. The cycle proof is shorter; this larger certificate is retained because it is the one proved by the existing Lean development.
.ZF
.bp
.ZH
.NH 1
Feasible small cases and formal correspondence
.ft R
.ps 11
.PP
For context, supplied face witnesses exist in the following small cases. Decimal entries were rationally reconstructed with denominator at most one million, then every sign and elementary submodular inequality was checked with exact rational arithmetic. The last column gives a constant-coordinate shift.
.TS
center box;
r r r r r r.
d	r	face bits	face points	inequalities	C
_
2	2	3	8	6	2
3	2	6	64	240	4
3	3	7	128	672	1283/177
4	2	10	1024	11520	10
.TE
.PP
For $t$ nonconstant bits, the elementary inequalities are
.EQ
h(A) + h(A cup "{"i,j"}") <= h(A cup "{"i"}") + h(A cup "{"j"}"), ~~~ i,j ~ notin ~ A.
.EN
Their number is $left ( pile {t above 2} right ) ~ 2 sup {t-2}$. They imply full submodularity: rearrange as diminishing returns for adding $i$ before or after $j$, iterate along an inclusion chain, then sum the marginal comparisons for elements of one set outside the other. This gives the arbitrary two-set inequality.
.PP
Extend a witness by $H(z,m)=h(m)+C(1-z)$ with $C >= -min h$, where $z$ is the constant coordinate. The added term is modular, so $H$ is submodular; the entire $z=0$ slice is nonnegative, since no monomial image lies there. On $z=1$ the signs agree with the witness. Clearing denominators gives integer-valued full-cube separators. The dossier stores these reconstructed integer witnesses. These cases do not classify every smaller or every other parameter.
.NH 2
The exact Lean assertion
.ft R
.ps 11
.PP
A point in the packet is a finite set of finite subsets of $roman Fin~d$. It is allowed at degree $r$ if each label has cardinality at most $r$. The allowed points form exactly the Boolean lattice on the low-degree labels, including the empty label. The function \f(CWphi\fP is the filtered powerset of the input support: the source monomial map in coordinate-labeled form.
.PP
\f(CWSeparator d r f\fP requires submodularity for every two allowed points, negativity on every image point, and nonnegativity on every allowed point outside the image. Values on disallowed points impose no constraint and can be extended arbitrarily. \f(CWSeparationExistence\fP universally quantifies over natural numbers $d,r$ with $r<=d$, demanding an integer-valued separator for each pair.
.PP
\f(CWSeparator.lean\fP proves permutation and group-sum bridges. \f(CWCertificate.lean\fP inserts the empty label in \f(CWdecode\fP, proves finite permutation identities and the thirteen-row contradiction, and specializes the universal assertion at $d=5,r=2$. Its endpoint is:
.DS L
.ft CW
Separation.source_existence_refuted :
  not Separation.SeparationExistence
.ft R
.DE
This refutes bare existence, hence the stronger efficient-evaluation assertion. The packet does not formalize a complexity model or a separate bijection to a numerically indexed cube; the coordinate-model identification above is a semantic correspondence checked in the supplied independent review.
.ZF
.bp
.ZH
.NH 1
Verification, evidence and trust limits
.ft R
.ps 11
.PP
This manuscript preparation ran neither Lean nor a kernel checker. The reused packet has SHA256
.DS L
.ft CW
.ps 8
441cb79ec825366931cdee6221b99e4b3235dd2145f343565e8df2fb2bd13db8
.ps 11
.ft R
.DE
and is copied byte for byte. A fresh safe-extraction test rejected path traversal, absolute paths, duplicate names and symbolic links, bounded the total uncompressed size, and hashed each extracted file. This tests archive safety and integrity, not theorem validity.
.PP
The discovery and independent-review records report strict extracted rebuilds with Lean 4.34.1 and an explicit-module \f(CWleanchecker\fP pass. The review reports all 45 local declarations passing its metadata and transitive-axiom audit; the final theorem uses only \f(CWpropext\fP, \f(CWClassical.choice\fP and \f(CWQuot.sound\fP. The packet includes Names, Separator, Certificate and audit modules. Its README identifies read-only mathlib cache revision d13f23b723b8a846827a245b89c10fc7d3f11612. These are recorded checks, not newly executed checks. The trusted upstream cache was not rebuilt in full.
.PP
The review retains corrected failed attempts: a missing-numpy run, an exact-decimal reconstruction problem and an audit count-type error. Its final successful receipts support its conclusions. Our fresh rational checks do not import discovery or review code and confirm both obstructions and all four small witnesses.
.PP
Parent-final replay and registry-refresh receipts are checked again at dossier finalization. Exact presence and contents are recorded in \f(CWresults.json\fP; absent receipts mean pending, not pass. Frozen input files are hash-bound before and after preparation. The dossier preserves the exact MathDB raw line, source bodies, HTTP receipts, review, retention report and root rulings. No acceptance or campaign-count change is made here: context is 43 of 60 beyond the prior 39, with zero credit assigned by this lane and root alone accepting.
.NH 2
Version and provenance qualifications
.ft R
.ps 11
.PP
The read source is the 2019 preprint [1], not the 2022 SICOMP version of record. The journal title expands "CSPs" to "Constraint Satisfaction Problems." Its author-listed metadata are SIAM Journal on Computing 51(3) (2022), 577-626, DOI 10.1137/19M1291054. Access was denied in the supplied investigations. We have not read the journal body and do not certify retention of the conjecture's wording, numbering or scope.
.PP
The retention report concludes NOT DETERMINED. Author lists link the open copies but do not certify journal equivalence; the thesis investigated is a coding-theory thesis, not a reproduction of this paper. The later root ruling permits packaging on this author-side evidence with a qualified limitation. That administrative decision does not close the textual evidence gap. The conjecture is unchanged in the read open copies. Bounded searches cannot establish absence of all later corrections or prior counterexamples.
.PP
A minor provenance inconsistency is preserved: the review cites a raw \f(CW341850.json\fP path, while the frozen record is \f(CW341850.jsonl\fP. Its recorded raw hash matches the complete file including its terminal newline. The raw record's "open" status and appended informal commentary are historical metadata, not mathematical premises or novelty certificates.
.ZF
.bp
.ZH
.NH 1
Related work and scope
.ft R
.ps 11
.PP
N\[:a]gele, Sudakov and Zenklusen [3] develop submodular minimization under congruency constraints, including constant prime-power moduli, and relate correctness to forbidden set systems. That supplies the algorithmic context of the source question. The negative-set realization in Conjecture 3.33 is a separate assertion; its failure does not invalidate the prime-power algorithms.
.PP
Elbracht, Kneip and Teegen [2] provide the dependency-digraph obstruction used in our shortest proof. We credit their Lemma 4.1 and Corollary 4.2 explicitly. Their partial-lattice formulation applies on our constant-one face without requiring a symmetric order function. The concrete failing monomial instance is the content here; no new general obstruction is claimed. We make no priority claim for identifying this instance or for any part of its method.
.PP
Later work on congruency-constrained totally unimodular problems [4] and strictly delta-modular integer programs [5] develops related reductions and algorithms. The supplied bounded primary-body review found no resolution of the monomial-image separator assertion in those texts. Its registry and citation screens have coverage limits. They record what was checked, not exhaustive novelty clearance. No live search was performed during this preparation.
.PP
The significance is modest: an interior-parameter counterexample blocks the universal separator premise of a proposed hardness approach. Neither tractability nor hardness of modular submodular minimization for general moduli follows. A replacement reduction or restricted separator hypothesis would need its own analysis.
.NH 2
Reproducible dossier
.ft R
.ps 11
.PP
The primary numerical receipt is \f(CWreceipts/recomputation.json\fP. Fresh standard-library code \f(CWscripts/recompute.py\fP, invoked in isolated Python mode, constructs the coordinate actions, checks cycle rows and membership, expands the symmetric certificate on actual masks, and checks rational small-case witnesses. No Lean, SAT or ILP process is invoked. Heavy commands run alone with two-CPU affinity, CPU and wall limits, sampled process-group RSS monitoring, and \f(CWMALLOC_ARENA_MAX=2\fP. Output paths are confined to this directory. Page renderings and a visual inspection receipt accompany the PDF; see \f(CWREPRODUCE.md\fP for commands and trust boundaries.
.NH 2
References
.ft R
.ps 11
.IP [1] 0.35i
Joshua Brakensiek, Sivakanth Gopi and Venkatesan Guruswami. \fICSPs with Global Modular Constraints: Algorithms and Hardness via Polynomial Representations\fP. arXiv:1902.04740v1 (2019); ECCC TR19-013 (2019), Conjecture 3.33, Proposition 3.34 and Corollary 3.35. Journal metadata qualified on page 5; DOI 10.1137/19M1291054.
.IP [2] 0.35i
Christian Elbracht, Jay Lilian Kneip and Maximilian Teegen. \fIThe Structure of Submodular Separation Systems\fP. arXiv:2103.13162v2 (2021), Lemma 4.1 and Corollary 4.2.
.IP [3] 0.35i
Martin N\[:a]gele, Benny Sudakov and Rico Zenklusen. \fISubmodular Minimization Under Congruency Constraints\fP. arXiv:1707.06212v2 (2018).
.IP [4] 0.35i
Martin N\[:a]gele, Richard Santiago and Rico Zenklusen. \fICongruency-Constrained TU Problems Beyond the Bimodular Case\fP. arXiv:2109.03148v3 (2023).
.IP [5] 0.35i
Martin N\[:a]gele, Christian N\[:o]bel, Richard Santiago and Rico Zenklusen. \fIAdvances on Strictly Delta-Modular IPs\fP. arXiv:2302.07029v1 (2023).

.ZF
