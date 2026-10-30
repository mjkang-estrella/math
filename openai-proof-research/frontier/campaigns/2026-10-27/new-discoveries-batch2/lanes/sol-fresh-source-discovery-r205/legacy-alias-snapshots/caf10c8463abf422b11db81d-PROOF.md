# Proof, source comparison and exact scope

See main.tex/paper.pdf for a self-contained proof. The frozen original ordinary
proof is inputs/root-cascade-rate-candidate-r1/PROOF.md. Its old claims that
formal proof is absent are superseded, as is the preliminary supplement HOLD.
The original 20-file freeze and all nine mathematical source hashes were checked
before copying and again after preparation. Original mathematical sources are
preserved byte for byte; only the audit and packet tooling are new.

Primary source: Cénac–Chauvin–Noûs–Paccaut–Pouyanne, Bernoulli27(3) (2021)
2011–2039, DOI10.3150/20-BEJ1299, Conjecture4.2 p2037. Conventions:
Definitions2.5–2.12, Eq.(5), Proposition3.1 and Definition3.2. Preprint
arXiv2004.07893v1 Conj5.2 p39. Source grading is length |alphaLIS|+n-1.
With alphaLIS=[true], length equals n; no arbitrary enumeration is used.
The source does not formalize "geometrical rates" separately: the packet
uses the eventual Cr^n term bound with C>0,0<r<1. A tail bound implies it.

Actual endpoints, no residual premises, namespace CascadeRate:
* source_geometric_rate_refuted : ¬SourceGeometricRateClaim
* convergent_non_geometric : Summable(kappa sourceTree(fairAssignment sourceTree)
  [true]) ∧ tsum(that same series)≤2 ∧ ¬GeometricDecay(that same series).
Actual types are printed in evidence/OriginAudit.log, not inferred from names.
SourceGeometricRateClaim encodes all admitted binary source trees and positive
normalized laws, excludes infinite saturated stable source subtrees, and asks
geometric decay for all actual context alpha-LIS. Our ordinary argument excludes
even unsaturated prefix/shift-closed infinite subsets. Binary is an allowed
source alphabet and suffices to refute the universal rate assertion. No claim
of a nonfair convergence theorem or a process mixing obstruction follows.

SourceDefs literally implements context prefix, longest internal strict suffix,
alpha-LIS, probabilities on finite and infinite contexts, cascade product, and
Eq.(5)'s finite length sum. Default values outside valid inputs are not assumed:
factor-validity lemmas ensure all consumed product inputs are noninternal.
The constructed T is saturated, has unique infinite branch (01)^infinity and
fair positive q on both context kinds. SelectedFamily and SelectedCounting
prove all-index suffix exclusion and exact free-bit counts in the same class.
DepthArithmetic/DepthAnalysis close the nongeometric inequality; KraftSummability
supplies the classical fair prefix-code bound for any source tree. That helper
and standard counting are uncredited, not additional proposed outcomes.

The exhaustive origin audit has 360 declarations across all nine modules.
This includes private, generated and instance declarations, not just 152 authored
exports. Actual isUnsafe=false and isAxiom=false throughout; transitive axiom
sets are subsets of {propext,Classical.choice,Quot.sound}. The generated
CascadeRate.depth._unsafe_rec has isPartial=true but isUnsafe=false, isAxiom=false,
and no forbidden axiom. Its spelling is not an unsafe flag. It is a harmless
compiler-generated partial recursor for the total depth definition. Actual
formal endpoints depend only on the standard three axioms. No sorry/admit,
custom axiom, native_decide or unsafe proof is permitted by the audit.

Novelty/source evidence is attributed to the copied independent reviews, not
inherited from Lean PASS. The actual 20-page supplement SHA256 is
 d691c3a9935abf9e8a11f2cdfe09ed70cf28e287c6a739ba86a4a6283a06aa7e.
Its public archive publisher capture and access failures are recorded verbatim
in inputs/sol-cascade-source-prior-review-r2/{provenance.json,http.json,review.md}.
No blocked live Euclid route was retried. Prior registry screens are explicitly
dated (about07:05UTC29Oct2026), bounded, and not relabeled current. Root's
separate refreshed registry/final review remains necessary for acceptance.
No exact MathDB ID, global literature clearance or author identity is asserted.

Strongest objections: an older theorem/construction giving both fixed-alphaLIS
allocation and absence of stable subtrees would subsume this; alternate source
rate/minimality conventions would alter attribution; a nonempty internal suffix
in the selected family or infinite stable subtree would defeat the mathematics.
The paper answers the last two mathematically, not by finite diagnostics.
It does not settle global priority or the universal bare-convergence conjecture.
