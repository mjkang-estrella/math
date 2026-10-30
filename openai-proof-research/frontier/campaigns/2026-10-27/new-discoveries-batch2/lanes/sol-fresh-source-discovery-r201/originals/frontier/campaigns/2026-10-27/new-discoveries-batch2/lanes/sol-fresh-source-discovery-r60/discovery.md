# r60: arbor Ehrhart root-location conjecture — unresolved, credit 0

## Source selection and literal scope

Two fresh expert primary-source targets were screened. Mu–Welker, arXiv:2503.24076v2 (14 October 2026), Question 1.0, asks whether EVERY real-rooted polynomial with constant coefficient 1 and positive integral remaining coefficients is the face polynomial of a simplicial complex. The latest introduction and Kruskal–Katona criterion were read; the available sufficient criterion in that paper does not settle the question. This target was deferred, not declared solved, subsumed, or disproved. Tsallis entropy was recognized as previously investigated and excluded before investment. No active Bessel or exhausted listed family was pursued.

Selected: Frédéric Chapoton, *On posets and polytopes attached to arbors*, latest arXiv:2503.04247v2 (25 August 2025), **Conjecture 2.2**, Section 2.1. An arbor is a finite rooted tree whose vertices are nonempty disjoint blocks partitioning a finite nonempty ground set E. Write n=|E|, and D(v) for the union of descendant blocks including v. Its genuine polytope is

Q_T={x in R^E: x_e>=0, sum_(e in D(v)) x_e<=|D(v)| for every vertex v}.

The full claim is that **for every such arbor**, every complex zero of the literal Ehrhart polynomial E_T(m)=#(m Q_T intersect Z^E) is real and belongs to [-1,0), with multiplicities unrestricted. The latest source states that all arbors through n=12 were checked. No restriction to singleton blocks, paths, stars, or bounded n is permitted. A proof for one of those classes would not resolve the selected target.

Chapoton–Athanasiadis arXiv:2605.26916v1 (only version in retrieved current abstract; document date August 24, 2026) repeats the same assertion as Conjecture 1.2, referring to older numbering 3.2. This numbering discrepancy is not a mathematical result. The original journal is Math. Scand.131(3)(2025),401–449, DOI10.7146/math.scand.a-159563. The journal route redirected to a login page; no credentials, alternate bypass, or claim to have read the journal body. Exact published-body comparison remains HOLD, despite latest-preprint and 2026 repetition being available.

## Closest actual theorem bodies and subsumption bridge

Read early: Chapoton Proposition2.1 and its entire occupancy proof; Athanasiadis–Xiao–Yan arXiv:2603.11654v1 Theorems1.3–1.5, inclusion-exclusion proof and parking-map proof of magic positivity; Athanasiadis arXiv:2510.23903v2 initially, corrected to **latest v3** (24 January 2026) after reading the live abstract, Theorems1.2/1.3, Conjecture1.4 and the full first proof of Theorem1.3. Latestv3 explicitly says no progress is made on Ehrhart root-location. Its chain reversal identifies E with a shifted zeta polynomial; it does not establish real-rootedness of that zeta polynomial. A generic conclusion from the duality would assume the missing claim.

AXY proves magic positivity and real-rootedness of the **h-star polynomial** for a restricted octopus class. The Ehrhart polynomial and h-star polynomial are different transforms. This is a substantive failed bridge, not simply absence of an endpoint: the integral lattice diamond conv((1,0),(0,1),(-1,0),(0,-1)) has Ehrhart polynomial

2m^2+2m+1=(m+1)^2+m^2,

which is magic positive but has discriminant -4. Its h-star polynomial is (1+t)^2, real-rooted. The lattice count follows by summing 4j points in shells j=1..m. Thus magic positivity, even for an actual lattice polytope with real-rooted h-star polynomial, cannot imply real-rootedness of E. The diamond is NOT an arbor counterexample. Further restrictions might yield a bridge, but none was proved here.

The two lexical Omega Chapoton hits were body-read at immutable latest-observed head6c27b0a84f560fa3e43d128d8a7f9e5f247e0be3: ChapotonConjectureFiveFourRefutation and ChapotonPropositionFiveTwoRefutation concern Chapoton–Han's 2020 Poupard/Kreweras formulas and literature-attested misprints. They do not concern arbor polytopes. This semantic comparison clears only these two bodies, not the registry as a whole.

## Route 1: exact root attachment and interval testing

Let root block size be r>=1 and child subtrees T_i have total size N, so n=N+r. For every integer m>=0, multiply their actual height distributions:

W_m(X)=product_i F_(T_i,m)(X)=sum_s w_s(m) X^s.

Choosing root coordinates with sum l gives binomial(r+l-1,r-1) choices. Therefore

F_(T,m)(X)=[degrees <=mn] W_m(X)/(1-X)^r,

E_T(m)=sum_s w_s(m) binomial(mn-s+r,r).

This is the public Proposition2.1 in equivalent form, not a claimed discovery. The fiber bound mn-s is nonnegative because s<=mN. The disjoint choices of child points and root coordinates prove the formula on all nonnegative integers. It covers all block sizes and branching patterns and is a correct algorithm for the original object.

The exact checker constructs height arrays, interpolates E over QQ using finite differences at 0..n, and checks an extra value n+1. Polynomial identification uses the source lattice-polytope/Ehrhart premise; the extra evaluation is an independent consistency check, not a proof of the all-tree root claim. Squarefree factorization and rational Sturm counts count roots in [-1,0] with multiplicities. Direct coordinate enumeration independently checks nine small source arbors; the public octopus inclusion-exclusion formula independently checks416 values. The bounded sample results are in SUMMARY.md and JSON logs. No universal inference from them.

Direct stability of the height polynomial cannot be the invariant: already one singleton leaf at m=2 gives F=1+X+X^2, with discriminant -3. A different transform/invariant is required.

## Route 2: moments and rational residues

Let E(m)=sum_s w_s(m), M(m)=sum_s s w_s(m), and Q(m)=sum_s s^2 w_s(m) for a forest of size N. Attach a singleton root, put B=(N+1)m. Direct finite sums give, for every nonnegative integer m,

G(m)=(B+1)E(m)-M(m),

2 M_new(m)=(B^2+B)E(m)+M(m)-Q(m).

Indeed sum_(l=0)^(B-s)1=B-s+1, while sum_(l=0)^(B-s)(s+l)=((B^2+B)+s-s^2)/2. The weighted Ehrhart moments admit polynomial continuations; the checked finite interpolation data are only diagnostics of these continuations. For disjoint forest components the pointwise product rule gives

M/E=sum_i M_i/E_i.

These identities suggest tracking the residues of the rational function M/E. If a reduced E has simple poles rho_j, all residues c_j of M/E are positive, and its polynomial part is a m+b, then

G/E=(N+1-a)m+1-b-sum_j c_j/(m-rho_j).

If N+1-a>0 this expression is strictly increasing between poles, because its derivative is N+1-a+sum_j c_j/(m-rho_j)^2. It has one zero in each intervening interval and one in each exterior interval. Common factors of E and M remain factors of G. To locate exterior zeros within [-1,0], endpoint signs must also be controlled. This is a conditional root mechanism; neither the residue condition nor all necessary endpoint conditions have been proved uniformly for reachable source states.

The second displayed update shows why first moments alone do not close an induction: after attachment one needs Q; subsequent moment updates need still higher moments. Positive residue evidence for small reachable trees is recorded, but it is not closure under attachment, and does not address arbitrary root blocks r>1.

A precise obstruction defeats a weaker induction. Take

E(m)=(m+1)(2m+1), M(m)=2m(m+1)^2.

For each integer m>=1 this is a nonnegative integral height distribution with w_0=m(m+1), w_(2m)=(m+1)^2, total E, support in [0,2m], and first moment M. At m=0 use w_0=1. E is the genuine dimension-two simplex Ehrhart polynomial and has roots -1,-1/2. Nevertheless, applying the singleton-root identity to this ARTIFICIAL profile gives

G(m)=(3m+1)E-M=(m+1)(4m^2+3m+1),

whose quadratic discriminant is -7. Thus real-rooted E, nonnegative integral masses and the honest dimension/height bound DO NOT suffice for root closure. The fake profile is not a simplex's actual height distribution and is not a source refutation. Its negative residue is precisely the information the proposed stronger invariant would need to exclude.

## Exact remaining gap and strongest falsifier

The full mathematical target remains unresolved. A rigorous promising next step would prove a height-moment/resolvent invariant for every reachable arbor forest, establish its preservation under every root attachment of EVERY positive block size, and deduce all roots are real in [-1,0]. The singleton-root residue condition alone is not the full target. Neither its uniform proof nor a higher-block closure is supplied.

The strongest direct falsifier is one genuine arbor, encoded by positive block sizes and its finite rooted tree, whose literal E has a certified nonreal zero or a real zero outside [-1,0]. A negative residue at a genuine source state would falsify the proposed invariant, but would not itself refute the source claim. Conversely, a prior public all-arbor proof or a complete same-object classical bridge would defeat discovery eligibility. No known-public theorem, formalization, helper identity, special case, finite verification, correction or obstruction is nominated for credit.

## Freshness, failures and delivery limits

Current source abstract pages and live raw Omega README were fetched normally. GitHubAPI403 inherited from r58/root was respected; no API retry. Latest observed Omega head is inherited15:49UTC, not claimed current16:xxUTC. r57 omega-D5.json is explicitly Blueprint/D5 markdown, not Lean D5. Cached scoped path screening and actual closest bodies are bounded evidence only; no byte delta across markdown/Lean trees. No complete latest registry head/tree refresh and no exhaustive prior-art coverage: freshnessHOLD, noveltyHOLD.

All numeric helpers used copied read-only capped_run.py: AS512MiB, sampled process-group RSS512MiB, CPU210s, wall230s, BLAS1. Failed imports, domain error and capped large runs are retained; workloads were reduced, caps unchanged. Details and receipts in failures.md/provenance.json. No PROOF.md because no full proof/refutation; no Lean investment, paper, nomination, acceptance/count edits, git/shared/other-lane writes, children, browser/account/contact/post/upload operations. Root remains7additional/37total; this lane credit0.
