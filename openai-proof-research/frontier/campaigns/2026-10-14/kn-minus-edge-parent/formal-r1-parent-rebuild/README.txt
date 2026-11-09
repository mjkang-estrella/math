Scoped Lean support for K_n with one edge removed
Myeongjin Kang — no affiliation
Original prose: CC BY 4.0. Original Lean/Python/configuration: MIT.

This directory supports the new algebra in the reviewed paper proof. It is
NOT a full formal certificate of the crossing-number theorem. The candidate
is not accepted or counted here, and no independent formal audit is claimed.

The manuscript claim is unchanged: for every integer n >= 2 and every edge e,
ordinary cr(K_n-e) equals
  Z(n) - binom(floor((n-1)/2),2)
  = floor((n+2)/2) floor((n-1)/2) floor((n-3)/2) floor((n-4)/2) / 4.
The path-product corollary covers every m >= 4 and n >= 1, with P_n having
n EDGES, by Ouyang–Wang–Huang Corollary 5.1. It is one application of the
same package. These full statements remain mathematical paper claims;
no Lean declaration in this directory asserts either crossing number.

What the Lean source proves

KnMinusEdge.lean uses actual finite tensor coordinates, finite-dimensional
linear maps and multivariate/univariate polynomial rings. Exact exported
types and every #print axioms report are in logs/final/types-axioms.stdout;
the examples have a separate example-types-axioms.stdout. Checks.lean and
ControlChecks.lean reproduce these audits. See coverage.json for the named
scope matrix; the final receipt records the exact counts and source hashes.

* tensor_kernel_iff proves that two zero functional contractions on a finite
  coefficient tensor are equivalent to a finite sum of rank-one tensors
  with both factors in that functional's kernel. It constructs projected
  basis vectors from an explicit normalized witness phi(e)=1. This is the
  tensor algebra in Lemma 3.1, not an equivalence between every zero crossing
  test and the missing-pair conditions. missingFunctional and its normalized
  witness also formalize the actual antisymmetric polynomial evaluation.
  The identification of finite coordinates with the bounded polynomial
  tensor product and the graph-cycle application are not formalized.

* slotEval_surjective and slot_kernel_dimension prove the evaluation loss
  d^2-d in finite tensor coordinates. split_kernel_dimension is the general
  surjective rank-nullity statement. The symmetric polynomial basis and
  its count d=binom(s,2) are still a paper-to-coordinate interface.

* diagonal_nondegenerate constructs and proves nondegeneracy of the actual
  weighted diagonal bilinear form from nonzero weights. mixed_dimension_bound
  and mixed_coordinate_bound prove dim(A)+dim(B) <= number of coordinates
  for mixed orthogonal images, with BOTH injection hypotheses visible.
  No direct-sum hypothesis or self-orthogonality hypothesis is used.
  delta, mixed_test_degree and mixed_test_missing formalize the actual
  PQ Delta product, its separate degree 2(s-2)+3=n-2 and its two split
  missing-pair conditions. Delta's two endpoint sign reversals and its
  nonvanishing on four distinct coordinates are proved.

* Rectangle uses actual MvPolynomial.degreeOf for u and v. orderPair is the
  explicit finite weighted evaluation sum. twisted_detector proves the
  consequence for A in P_(d,d), tests B in P_(d+1,d), from full rectangular
  right nondegeneracy on P_(d+1,d) x P_(d,d+1). It proves (v-c)A=0 then
  cancels the nonzero polynomial. It does not invert the twist at nodes.
  In manuscript notation s=d+2. The square detector is not substituted.

* twisted_detector_from_U4 makes the exact upstream premise inspectable:
  2(d+2) distinct REAL nodes; arbitrary order given by a permutation;
  weights 1/G'(t_i); signs +/-1/2; full rectangular right nondegeneracy.
  UpstreamDetectorPremise is a defined proposition passed as an EXPLICIT
  argument, not an asserted axiom or a theorem proved in this package.
  U4 is stipulated mathematics at the pin specified below. Its proof is
  not formalized. The generic twisted deduction works over any field.

* localTest, local_test_degree, local_test_first_missing and
  local_test_second_missing use the full product
    P (u-v)(u-y)(v-x) U(x) (y-a)V'(y) (v-a)B'(u,v).
  With d=s-2, the budgets are P: (d,d,d,d), U: (d+2,0,0,0),
  V': (0,0,d+1,0), B': (0,d+1,0,d); the degree is at most 2d+3 in
  each variable. Both added missing-pair factors are present.

* linear_zero_of_products proves the polynomial span of products with
  budgets r,t using monomial splitting. localize_away constructs the actual
  Lagrange isolator, divides it by X-t_a, and uses its real natDegree bound.
  It isolates any i0 != a from all the displayed summed equations, with no
  assumption about sigma at a or b. In the paper it is used only outside
  BOTH missing endpoints. localized_twisted_vanishing assembles this step
  with full rectangular detection at those complete stars. The summed
  equations and their identification with the local order pairing remain
  explicit obligations. They have NOT been proved from a drawing in Lean.

* diagonal_root_bound works over Polynomial(MvPolynomial(Fin 2,K)) and
  proves zero from actual evaluations at the 2s-1 distinct nodes outside
  {a,b}, with natDegree <=2s-4. collision_divisibility is the univariate
  factor theorem over an arbitrary commutative coefficient ring.
  The four-variable collision polynomial C=(x-y)(x-v)(u-y)(u-v), its
  separate degree two, nonvanishing at independent pairs, and invariance
  under BOTH within-pair swaps are proved. Its specialization at (a,b)
  is a NONZERO POLYNOMIAL in (y,v); it need not be nonzero at every point.

* quotient_preserves_missing cancels that nonzero specialized polynomial;
  quotient_preserves_symmetry and quotient_preserves_evaluations give the
  other cancellation steps. quotient_degree_loss gives exact degree loss.
  degree_descent proves well-founded termination under an explicit
  factor-and-preservation obligation for a predicate W. It does not prove
  that obligation for the manuscript kernel, and no injection is smuggled
  into an upstream hypothesis. small_degree_collision_zero handles d=0,1,
  with separate s=2 and s=3 examples, without negative degree spaces.

What remains unformalized

The paper proves injectivity of E on S_a by localization, roots, the FOUR
prime collision factors and preservation under descent; it proves the
S_b injection by the edge-slot swap. BOTH claims remain paper claims here.
The missing Lean assembly includes: the oriented graph edge-chain and drawing
model; barycentric cycle construction and application of graph-general U2;
identification of the tensor/polynomial and symmetric-space bases; reduction
of the summed tests to complete-star pairings with exact local weights;
substitution P(x,u,x,v) and the transfer of its degrees; simultaneous prime
four-factor divisibility from the two symmetries; instantiation of descent
for the actual evaluation kernel; the S_b edge-slot permutation; and the
full connection of mixed orthogonality to drawings and crossing counts.

In particular the paper's ordered edge-pair support T counts both whole-edge
orders. Each fixed ordered pair has FOUR endpoint orientations, producing
four equal terms because J and Delta both reverse sign. Dividing the test
sum by four yields the mixed diagonal form with every coefficient nonzero;
ordered support gives c(D)>=|T|/2. Those graph/orientation/counting bridges
have not been formalized. The even responsibility argument, matching upper
drawing, all-n assembly and external zip-product theorem are also not
formalized. No restriction to two-page or rectilinear drawings is imposed
on the mathematical manuscript claim.

Examples and controls

Controls.lean contains nine kernel-checked theorems: a nonzero non-diagonal
3x3 admissible tensor; the six-dimensional split kernel for a three-vector
basis; a zero skew self-pairing outside the admissible kernel; dimension
counterexamples when injection or nondegeneracy is removed; a nonzero
constant invisible to every twisted test for invalid detector data, with
rectangular nondegeneracy explicitly refuted; five-rational-node isolation;
and separate s=2 and s=3 collision-degree cases. These are semantic
obstructions and examples, not assertions that altered code merely differs.

All-n computation is not substituted for proof. semantic_checks.py provides
finite exact integer/Fraction identities, including 101-digit integers;
all floors use // and ceilings use integer arithmetic. checked_run.py rejects
nonzero exits AND failure markers such as SOME FAIL even if a process exits
zero. Its two paths have enforced controls. Historical author checks mix
exact rational, finite-field, combinatorial and floating-point geometry;
they are not all rational certificates and were not rerun here. Their
printed generic invalid test is not an enforced negative-control assertion.
Independent proof-review early failures were corrected harness expectations,
not counterexamples to the mathematical proof. See responses-to-findings.json.

Build and verify

Pinned Lean: leanprover/lean4:v4.34.1, compiler commit
  5045d0056413266e57c625dcd7c365b10e377c52.
Pinned mathlib: d13f23b723b8a846827a245b89c10fc7d3f11612.
lake-manifest.json pins the complete dependency graph. No new axioms,
unfinished proof placeholders, unsafe declarations or native_decide are used.
All exported declarations and all control theorems are audited; the only
reported dependencies are propext, Classical.choice and Quot.sound.

From this directory, in this repository:
  python3 -B verify.py
  python3 -B verify.py --rebuild

The first command checks immutable byte/hash manifests, the frozen input
records and that the final build receipt matches the source. The shared
campaign ledger is a historical context record: its original hash is retained
but live progress edits do not alter the fixed proof/build inputs. See
logs/context-change.json and the retained initial verification failure. The second
also compiles fresh copies of all four .lean files, runs every type/axiom
query and the controls, and stores a new receipt in .replays/. It never
updates manifests or reseals evidence. No previous package .olean is used.

The default compiler/cache paths match the existing local environment:
  /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean
  ../formal/.lake/packages
Their dependency libraries are used READ-ONLY. Build objects and disposable
copies stay in this directory. Version, dependency revisions, command lines,
complete stdout and stderr, source hashes and axiom reports are retained in
logs/final/. Other compiler/cache locations can be supplied:
  python3 -B verify.py --rebuild --lean /path/to/lean --cache /path/to/packages

A detached copy can verify its own payload with:
  python3 -B verify.py --payload-only
A conventional independent Lake build uses the pinned lean-toolchain and
lake-manifest.json, fetches dependencies into THIS project's .lake/packages,
then runs 'lake exe cache get' and 'lake build'. This route requires network
and a matching Lean installation; it was not run during this assignment.
The executed route compiled our source from scratch with the existing
pinned dependency cache. It did not rebuild mathlib or modify its cache.

Evidence, attribution and rights

candidate.md SHA256:
  2a078a07142986c93845f4855496db14e41ee2590adc17720727b19145dd1c8b
Independent proof review SHA256:
  1d18d360eb4a50ae801c00b56ffe377b599c9c28c9ecd4cb3753e559f45aa111
Independent contribution review SHA256:
  a481ddd9c10bb938f587cd1e2ad9baa756d8ae7ae4c37c2bae3a48023395f557
All were read, authenticated and left unchanged. Parent proof PASS and
SUBSTANTIAL-one-package dispositions are inputs, not conclusions of this
implementation. The contribution review's historically pending-proof
language is preserved. source-record-audit.json independently authenticates
24 original source entries, 9 candidate outputs, 19 proof-review outputs,
and 5 contribution-review outputs. Input and output manifests are separate.
Development logs and the first failed log-parser run are retained as
implementation history, not proof counterexamples. logs/final is authoritative
for this source revision; earlier receipts name their earlier source hashes.

Upstream mathematics is stipulated true at OpenAI/math commit
  fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
The exact file and U1-U6 contracts, especially U4, are in source-contracts.json.
The new mathematical portion is the odd lower bound n>=15. Even n, odd n<=13
and the upper bound are credited consequences of the pinned complete-graph
formula and Ouyang–Wang–Huang / Chia–Lee / Zheng et al. Corollary B is one
application using OWH Corollary 5.1, first using the new portion for odd m>=13.
Zheng's original 2007 article was not obtained: attribution is through the
obtained OWH text and the contribution review's exact survey/Chia–Lee
locators. No direct reading of Zheng is claimed. Sadhu's contemporary
bipartite one-edge result is an antecedent; the reviewed compression and
three-edge completion operations differ from this kernel/split-space/twist
construction. Neither wholesale independence nor global priority is claimed.

No publisher reading materials or dependency source/object files were copied
into this payload. Existing sources remain read-only and retain their own
rights. See LICENSE.txt and provenance.json. No shared index, acceptance,
count, staging, commit, public upload, submission or message was made.
