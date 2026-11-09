# Independent full formal review

Formal verdict: PASS for this frozen literal endpoint. Source fidelity: PASS for the independently posed
four-variable bound. Prior-art clearance: bounded HOLD. Substantive status:
qualified continued consideration, with root adjudicating acceptance and credit.
This review does not accept or count an outcome. Counts remain 9 additional /
39 total / next40. No children, network, shared, git, browser, public service,
MathDB, manuscript, or candidate edits were performed.

The assigned source-only archive was bound before extraction or scientific
inspection to SHA256
`17ba800adb3154f5c3929ef076c47b9d1f0adaace1576793faa4154ff19be13f`.
All work is local to this assigned review lane. Administrative ledger/context
files are snapshots; scientific bindings and immutable predecessor references
are separately recorded and rechecked. Candidate receipts are evidence of its
claims, not this review's replay evidence.

## Exact mathematical endpoint and source

For every positive natural m, indexed a : Fin 4 → Nat with each a_i < m, and
K < m, the conclusion is

sum(j=0..K) sum(T subset Fin4) (-1)^(4-|T|)
floor((j+sum(i in T) a_i)/m) >= -3 floor(m/3).

`FloorSums.LiteralEndpoint` has precisely these binders; the sum and inequality
live in integers. `Source.actual_source_sum` identifies natural division with
the actual real floor. There is no distinct-entry premise. Subsets are subsets
of indices, so repeated values remain independently indexed; the empty subset
is retained with its positive coefficient. The endpoint includes m=1, K=0,
K=m-1 and zero/equal entries without excluding any boundary.

I read the frozen primary text of Thanatipanonda–Wong, *Curious Bounds for Floor
Function Sums*, JIS21 (2018), Article18.1.8, introduction pp1–3 and Section4
pp14–15 including the complete Theorem15 proof, the subsequent Conjecture17 and
publication line. The official primary PDF is
https://cs.uwaterloo.ca/journals/JIS/VOL21/Wong/wong7.pdf,
SHA256 `345c2cf3893d3c2c0371e0b2053bf02c6f04469243f7c1ca33e1d0681fc15d7d`.
Section4 independently poses exactly this uniform-m lower bound; Theorem15's
proved bound is only -2 floor(m/2)-floor(m/3). Its proof combines two-/three-variable
estimates and does not establish the requested endpoint. The full later
Conjecture17 includes other dimensions and extremizer assertions, and is not
claimed solved. Published February23,2018; the frozen prior review records
arXiv v1 August10,2017 and v2 February14,2018. I did not retrieve historical
arXiv versions afresh.

I also read the actual Onphaeng–Pongsriiam2017 Theorem9 and complete proof,
pp14–19, equations43–60 and conclusion, with publication line January14,2017.
Primary PDF https://cs.uwaterloo.ca/journals/JIS/VOL20/Pongsriiam/pong11.pdf,
SHA256 `ca380dff9a0d4018c12ae8f96a2ad0712d2b75dbef83d4835b0c8d5bb5187ea9`.
The proof groups signed two-variable blocks. At dimension4 the stated bound is
±4 floor(m/2), and its displayed grouping gives the better lower estimate
-3 floor(m/2), still insufficient. Even-dimensional sharpness concerns the
upper endpoint. Pointwise f/g extrema do not supply the missing prefix bound.

## Proof interfaces and generated semantics

The four inherited modules Reduction, Symmetry, Source and Expansion are
byte-identical to both predecessor source archives. All 38 inherited arithmetic
modules, containing 1,329 implications, are byte-identical to r2. Byte identity
is checked against archive members, not inferred from receipts.

For H=K+1, every j+s is below 5m. Its quotient is the sum of the four indicators
lm <= j+s, l=1..4. `threshold_count` counts these as
C_H(s+H-lm), C_H(u)=max(0,min(H,u)); `literal_eq_clamped` sums this identity.
Sorting uses a permutation of Fin4 and transports every indexed subset, allowing
equal entries. `Expansion.explicit_sixteen` gives all sixteen signed summands.
`ClipBridge` proves the 64 actual query clamps; `SourceBridge` proves each
argument identity and `sum_match` by those proved equalities and additive
normalization. These are proved identities, not assumed source-query bridges.

`Assembly.Vars` contains exactly seven integer fields m,H,t,a,b,c,d. The source
scan verifies all 10,188 semantic definitions have an explicit integer or Prop
type and depend only on earlier definitions. An independent translation check
compares every definition body with the actual frozen DAG. Of 576 integer ite
definitions in total, precisely 128 correspond to fresh `z3name!` atoms; all
128 are concrete acyclic ite definitions. There are no fresh environment fields.
Integer equalities and propositional equivalences use their appropriate Lean
types; substitutions instantiate the byte-identical arithmetic implications
with the shared semantic expressions. Kernel replay checks each instantiation.

The structural review independently reconstructs all 12,459 reachable rule
nodes from the 22,672-node DAG. It checks every node theorem's conclusion and
explicit residual hypothesis binders, including all 644 lemma discharge rules.
Those rules contain actual classical proofs of the discharged assumptions;
Python deletion from a hypothesis set is not a proof premise. The 45 historical
Dag168 nodes now have actual origins parts.Dag168_000 through _044; the wrapper
only imports the final part.

`Assembly.n22671 (v : Vars) (q : Query v) : e7489 v`, with e7489 definitionally
False, has no residual hypothesis binder. `Query` is precisely the conjunction
of the seventeen used original assertions. The unused eighteenth assertion is
m >= 3t. Omitting it strengthens the contradiction obligation and causes no gap.
`query_of_neg_bound` derives every used assertion from the actual domain,
sorting and negated bound with sourceEnv setting t=floor(m/3). Hence
`Assembly.sorted_clamped_bound : FloorSums.SortedClampedBound` and
`Assembly.literal_endpoint : FloorSums.LiteralEndpoint` require no unproved
bridge, checker theorem, solver axiom, arbitrary fresh-symbol assignment, or
residual mathematical assumption. The named endpoint itself has no arguments;
the only hypotheses are the intended quantifiers inside LiteralEndpoint.

## Independent replay, exhaustive audit and reproducibility

The fresh extracted serial replay independently succeeded for all 437 mathematical
modules and all 22 exhaustive audit partitions (459 Lean invocations). The
streaming independent reader confirms exactly 35,654 declarations across 436
actual origins, with identical declaration/type/safety/transitive-axiom coverage
sets. The sole empty mathematical module is the Dag168 import wrapper. All 59
inherited source declarations and exactly 1,329 original arithmetic theorem
names are included; generated declarations beneath theorem names remain audited.
All owned definitions are safe, no owned partial declaration occurs, and every
unsafe flag is false. The only transitive axioms are propext, Classical.choice
and Quot.sound. No sorry/admit/new axiom, native_decide or solver/checker axiom
is present. Audit sources select all actual module origins, including private
and generated names. Declaration-name-set SHA256 is
`7abfdce5f2b7e1d6ba7df2fc0de7ee9a96faa975f113e04b512bfd42008a668b`.

The independently reconstructed gzip/tar has exactly the assigned archive hash,
with all 499 member contents matching the fresh extraction, deterministic zero
metadata and no own compiled artifacts. Maximum sampled Lean process-group RSS
was 2737586176 bytes; maximum individual wall time was
62.820 seconds. All invocations stayed within the unchanged
caps. Full actual types, safety and axiom reports are in replay/logs/Audit*.log;
independent-replay-receipt.json records the independent result. The reader's
initial arithmetic prefix-count failure and corrected exact-name rule are
preserved and explained in FAILURES.md.

The audited programs enumerate env.constants by actual module origin, rather
than selecting public declaration names. The review checks their selection is
an exact partition of all 437 mathematical source modules. Private/generated
declarations and instances are included; audit/display modules are excluded
from mathematical origins. There are 460 Lean files in the archive: 437 replayed
mathematical files, 22 audit partitions and the unused legacy Audit.lean display
program. The latter is not an omitted mathematical proof module.

The authorized Lean binary hash matches
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
The full inherited and actual mathlib pin is
`d13f23b723b8a846827a245b89c10fc7d3f11612`; it resolves the abbreviated root
transcription. All nine actual package heads match the inherited pins. No git
operation was used: pin metadata was read directly.

The archive is a source certificate for the pinned environment, not a portable
standalone toolchain distribution. replay.sh and lean_guard.py require the
specified absolute helper/Lean/package paths. Generation and historical
provenance scripts reference immutable predecessor material intentionally not
recursively bundled. This limits standalone regeneration of the whole research
history; it does not add a mathematical assumption to source compilation.
Archive byte reproduction and compilation are separate checks.

All helpers use the assigned helper_guard, environment thread limits and fixed
512MiB AS/group RSS, CPU210/wall230. Lean alone uses the explicitly authorized
separate -j1 -M2700, groupRSS2800MiB, CPU210/wall230 path, with no additional
AS512MiB restriction. Invocations are strictly serial. RSS is sampled, so no
claim excludes unsampled transients. Disposable local compiled objects are
removed only after successful audit; source and full logs remain.

## Prior-art and substantive boundary

I read the frozen source/prior-review-r2 and computational preliminary-review-r1
reports. Their independent mathematical checks and bounded search coverage are
inherited with their actual limits. The prior reviewer read the 2019 one-subset
formula, 2021 floor-sum body and selected 2022 absolute-value inclusion–exclusion
proofs. I do not claim to have independently reread those bodies. The published
one-subset identity, threshold reduction, sorting and Presburger decidability
are classical/routine ingredients and earn no separate credit.

The documented absolute-value bridge expresses the desired sum as joint
differences of shifted g4 values. Lower bounds for the individual values do not
bound those differences. Likewise the older block bounds do not control joint
extremality or resolve both nonzero residue classes modulo3. No complete
published subsumer or short classical derivation was established in the bounded
review, but absence was not proved. Root must still judge whether resolving
this separately posed full fixed-dimension source question by a standard solver
and an exact certificate meets the substantive campaign standard. Certificate
size and formalization alone do not settle that judgment.

Current public-registry head/content remains unavailable. The pinned registry
screen is index coverage, not current proof-body clearance. Carlitz1960,
Jacobsthal1957, Carlitz1959, Grimson1974 and four metadata-only citing bodies
remain uncleared; no new network retrieval or route retry occurred here.
Denied GitHub API/raw/codeload/diff/patch, ScienceDirect and Google challenge
routes remain parked; no proxy, TLS-disable or browser bypass was used.
Chronology and bounded coverage do not certify worldwide novelty.

The review's failures are preserved in FAILURES.md and the candidate's earlier
failures remain frozen. provenance.json, original-source-bindings.json,
binding.json and immutable-references.json record exact scientific dependencies.
The final manifest excludes itself and its verification receipt; a separate
guarded verifier runs after substantive writes and rechecks coverage, every
hash, original/copy identity and pinned revisions. No acceptance or manuscript
gate is silently cleared by this integrity receipt.
