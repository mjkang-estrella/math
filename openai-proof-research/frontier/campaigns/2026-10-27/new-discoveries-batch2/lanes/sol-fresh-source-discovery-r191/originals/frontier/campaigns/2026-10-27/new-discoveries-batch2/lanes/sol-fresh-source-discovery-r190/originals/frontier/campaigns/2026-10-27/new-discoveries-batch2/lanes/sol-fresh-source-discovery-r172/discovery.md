# r172 — zero eligible outcomes

Work solo in the assigned lane; no children, Lean, manuscript, shared writes,
git, count changes, messages, uploads, browser or public actions. Root owns
adjudication. Observed tally: 9 additional / 39 total, next 40.

## Historical screen and choice

Read ancestor/batch AGENTS, ledger and prior-campaign accepted scopes, latest
NEXT handoffs, and original r169–171 summaries. The latest root decision
excludes prefix reversal as classical adaptation; cycle congruence remains
unresolved; pendulum is separately in preparation. None was reopened.

history-receipt.json reuses the r171 qualified index (itself descended from
r169/r168), refreshes changed hashes and immediate original lane reports,
and retains r111–113 explicitly. It lists 1,735 exact paths, six changed/new
records, no missing indexed files. inherited-history-qualification.json
preserves the prior byte-identical counterpart evidence and its bounded
coverage policy. No additional old file was excluded as an echo here.
Exact arXiv/DOI/title/author/statement-alias search is exact-screen.json:
no matching original investigation for the two selected questions. This is
not worldwide clearance. lead-screen.json preserves the failed Leake lead:
Q1.7 is old r52/r77/r80/r102/r129, so dropped without reopening. Its unrelated
Leake name hits also remain. statement-screen.json preserves noisy generic
descent hits; exact-screen.json narrows them without deleting evidence.

registry-screen.json preserves the initial raw-line screen, including SHA
substring false positives from `63561`. registry-path-screen.json corrects
that method by parsing tree paths; remaining EJMScoreSymmetry hits are caused
by the broad `jmsc` substring, not mathematical matches. No same-target saved
path was identified. Saved catalogue paths/hashes are explicit. No current
whole-registry clearance, missing-merge reconstruction or new denied-route
request is claimed. Actual current arXiv/source bodies take precedence.

## A. Full Reed–Solomon minimum-subpacketization claim — UNRESOLVED

Primary: Weijun Fang, Jing Qiu, Shu-Tao Xia, Fang-Wei Fu,
*The Minimum Subpacketization of Reed-Solomon Codes with Linear Repair
Achieving the Cut-Set Bound*, arXiv:2610.37522v1, 27 October 2026,
Section VI, Conjecture 1. Actual HTML and actual TeX archive obtained and
read: Definitions 1–2, repair/evaluation lemma, helper alignment,
Propositions 1–3, Lemmas 3–5, Theorems 3–6 and conclusion; relevant proof
bodies, not just abstract labels. The unversioned abstract accessed at
03:08:36 UTC on 30 October lists only v1 and no journal reference. That
establishes this accessed history, not exhaustive publication clearance.

Literal target: for every prime power q and integers 3 <= k < d <= n-1,
with s=d+1-k,

    ell_min(n,k,d;q) = s Delta_s(n,d).

Here ell_min minimizes extension degree ell for an ordinary (n,k) RS code
over F_(q^ell) admitting exact F_q-linear cut-set-optimal repair of EVERY
coordinate from EVERY d-element helper set. Delta minimizes lcm(a_1,...,a_n)
over positive integer labels with

    lcm(a_i, a_h : h in H) / lcm(a_h : h in H) >= s

for EVERY d-subset H and EVERY i outside H. No fixed-q, fixed-k, asymptotic,
generic-evaluation, partial helper-set or parameter-instance result is claimed.

The source proves the universal upper bound. Its Proposition 3 gives, for
every actual admissible code and every H,i, writing m(X) for the degree of
the cross-ratio field of the evaluation points indexed by X,

    m(H) | ell/s; m(H+i)/m(H) >= s; m([n]) | ell/s.

Thus a sufficient all-target missing step is a feasible n-tuple of integer
labels whose lcm is at most m([n]) for every such code. Equality representation
of every m(H) is stronger than necessary. The source already supplies that
representation when 2d >= n+3 and a different degree lower bound throughout
d(d+2) >= 4(n+1). Reproving those ranges would receive no credit.

### Sustained uniform route and why it does not close

The attempted route was simultaneous projective normalization, then prime-by-
prime encoding of the local field-degree constraints. For sets X,Y sharing
three points, normalize those points to infinity,0,1. The normalized coordinates
generate each cross-ratio field, so m(X union Y)=lcm(m(X),m(Y)). The source's
Lemma 5 then produces the required coordinate labels by minima of valuations.
This is an actual complete classical/source bridge on the overlap domain,
not a new result or evidence that the unrestricted extension follows.

The unrestricted lcm identity is FALSE even over a finite field. In
E=F_3[t]/(t^2+1), let

    A={infinity,0,1,2}, B={infinity,0,t,2t}.

A is the standard F_3 subline and B its scalar multiple, so both cross-ratio
fields equal F_3. Their union contains the triple infinity,0,1 and t, hence
its cross-ratio field contains t and equals E. Thus their degrees are 1,1,2,
not 1,1,1. Applying y -> 1/(y-(1+t)) makes every point finite; its pole lies
outside the union. The encoded finite set is {0,7,3,8,2,4}, with a+3b encoding
a+bt. Projective invariance preserves the obstruction. This is an ordinary
exact proof; the 360 checked quadruples only independently check the arithmetic.

Crucially this is NOT a conjecture refutation. With d=4,s=2 the configuration
fails 24 local repair degree conditions. No admissible code or full Delta
comparison was constructed. It only kills the indiscriminate lcm bridge.

A more flexible prime-level route remains open. For a divisor f of M=m([n]),
sets whose cross-ratio field lies in F_(q^f) are contained in projective
F_(q^f)-sublines. Two distinct such sublines share at most two points:
normalize any common triple; each becomes the standard subline, which forces
equality. At a prime level p^e of M, consider f=M/p^j. A helper set H can lie
in one subline while H+i leaves it. Different H can require different
sublines at the SAME prime level. Giving a prime factor to the complement
of a single chosen subline encodes only the corresponding local separations.
One must select compatible nested sublines/coordinate valuations over all
primes so that the product of retained relative factors is >=s simultaneously
for every H,i, with global lcm <= M. Neither the incidence fact nor local
relative-degree inequalities proves such a simultaneous selection theorem.
The actual repair spaces might supply extra compatibility; none was proved.

Using all absolute degrees after one normalization also fails as a proof:
three anchor coordinates become rational (degree 1), and cannot satisfy the
feasible-label condition when one is the failed point. Allowing a new
normalization for each H loses the single global tuple required by Delta.
Puncturing gives sG_s(d+1), exactly the source bound, without the missing n-
coordinate coupling. Private-factor arguments cannot just be extrapolated:
the source already tracks deficient coordinates with shared prime factors.

### Classical/public objection and actual-body comparison

The material prior body read is Tamo–Ye–Barg, FOCS 2017 pp216–227,
*Optimal repair of Reed-Solomon codes: Achieving the cut-set bound*.
Section IV Theorem 5 and its full proof (printed pp223–226) puncture to a
full-helper code, derive repair-space alignment, and use k-1 non-generated
field elements to obtain ell >= product of the first k-1 primes. That actual
proof does not furnish the all-n Delta-feasible tuple. The new source explicitly
credits this alignment argument; claiming it as a new theorem would be routine
adaptation. The source's own upper construction and existing overlap/quadratic
lower proofs are stronger immediate objections to any restricted nomination.
The cited Qiu2026 local-subspace theorem was read as quoted in the primary
source, not independently body-cleared. No complete classical subsumption
of the still-missing uniform step was established, and no eligibility PASS
can be given to an unproved claim. Bounded public exact-title/ID search found
the primary source; this is not proof that no resolution exists elsewhere.

## B. Two-variable monomial descent — PUBLIC COUNTEREXAMPLE; EXCLUDE

Primary: Folake Ayobami Amao and Melody Omofuewe Reginald-Ihedike,
*Monomial Ideals in Few Variables: Generators, Betti Numbers, and Regularity*,
FNAS JMSC3(1)(2026)94–100, DOI10.63561/jmsc.v3i1.1226, printed p96,
Conjecture 1: “No monomial ideal in k[x,y] exhibits descent”. The displayed
quantifier is mu(I^(s+1)) >= mu(I^s) for every s>=1 and monomial ideal I.
PDF and current journal landing bytes retained; landing dates publication
31 March 2026. Its neighboring false two-generator stabilization assertion
was noticed, but no correction of it is nominated.

Actual prior body: Eliahou–Herzog–Mohammadi Saem,
*Monomial ideals with tiny squares*, arXiv:1801.07672v1 (23 January 2018),
Theorem1.1, complete Section3 divisibility argument and Section4 construction,
especially Example4.2. The explicit ten-generator ideal there has square
with nine minimal generators, over ANY field. checks.py independently
reconstructs all 100 ordered products and their divisibility antichain,
giving exactly the nine displayed square monomials. The characteristic is
irrelevant because distinct monomials are linearly independent and divisibility
determines monomial ideal membership. This refutes the full universal
statement at s=1, but it is literally an explicit published prior example,
not a new resolution or discovery. No nomination. No claim concerning
associated-prime persistence or other assertions of the 2026 source.

## Delivery and limits

http.jsonl records actual UTC, URL, result and SHA256 of every successful
retrieval, plus the failed mistaken-v3 HTML request (404; actual TYB abstract
lists only v1). No GitHub API/raw/codeload/patch, ScienceDirect or Google
challenge requests, evasion, proxy or TLS change occurred. The helper guard
was unchanged, with 512MiB address space and sampled group RSS, 210CPU,
230wall, nominal40ms; unsampled transients are not ruled out. All helper,
retrieval, extraction and hash commands ran through it; native bounded reads
and apply_patch were used. Initial oversized native reads were truncated;
targeted accepted-scope/summary/source reads remedied that, without pretending
all of NEXT/CONTENTS was line-read. See progress.md for deviations.

Scientific freeze binds only lane-local immutable sources/snapshots and
research files, not concurrently changing shared NEXT or ledger originals.
finalmanifest.json excludes itself and its verification receipt; verify.py
independently recomputes file hashes and checks exact payload membership.
No full eligible survivor, Lean, paper, acceptance or extra count is asserted.
