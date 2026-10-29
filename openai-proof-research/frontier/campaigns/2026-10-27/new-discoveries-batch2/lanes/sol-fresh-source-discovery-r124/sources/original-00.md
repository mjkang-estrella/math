# Fresh source screening, 26 October 2026

No discovery count in this lane. Actual source statements override MathDB status
and automated reference notes.

## Exclude372585: exact endpoint proved in the cited paper

Zhang,2601.10602v1, actual Introduction and Theorem2.12/proof read.
Theorem2.12 states both hyperbolicity-cone membership of diag(A) and
P(diag A)>=P(eigenvalues A), exactly resolving its Conjecture1.6 (Le).
The proof uses Schur-Horn, Birkhoff and Gårding concavity; this is already
explicitly presented as a resolution, not a new research opportunity.
PDFSHA9cd8b83cff0abec40028a9d114a30e908a4403e1d6d25cfef65fa1bbccb9e022.
Primaryhttps://arxiv.org/abs/2601.10602 . No Lean/credit pursued.

## Exclude322910: actual2026 resolution located

Li-Zhou2608.20937v1, actual Introduction/Theorem1.1 read. It proves the
complementary McCarthy negative-exponent inequality for everyq<0 and records
that the positive reverse direction holds for allq>=2 by Audenaert norm
compression. Both unresolved ranges in MathDB322910 are covered.
PDFSHA11d4f35a0a632b5657a22c89b0eb19d1aa79196f4793d2f560dae883c8356d20.
Primaryhttps://arxiv.org/abs/2608.20937 . No new proof/credit pursued.

369147: exact MathDB statement itself says solved byLin-Zhang, and cited title
is a new proof. Not pursued; actual original proof body not separately read.
338858: mu=1 includes Soules' old refuted conjecture; no rediscovery credit sought.

##375724: reference-note conflation corrected, no research result

Mao-Wang2607.01572v1, actual Section4pp10–11 read. The source says Brändén-
Jochemko refuted real-rootedness preservation of the GENERAL Eulerian
transformation. That does NOT refute its own Conjecture4.1 for the rows of
A² andD², which is stated open afterward. MathDB's 'refuted according to
source' reference note conflates these different assertions.
An existing September2026 research repository advertises a proof of the D²
case; it must be read before any D² novelty claim. No such claim is made here.
Exact integer search throughn350 checked60726 Newton inequalities forA² rows,
with no failure. This is not a proof of real-rootedness and yields no count.
Script/output:screen_eulerian.py,eulerian-screen.json.
PDFSHA49bfed988ea490a3c34702fc4ec49910d95d085b8ec50a98f6e0f38012485917.

##374150/374151 finite freep-Stam: numerical reconnaissance only

Hashemi2604.11922v1 actual definitions(6)–(10), Conjectures4.1/5.1/5.2 and
Section6 read. A differential-evolution screen includes relative scaling of
the two root vectors, degrees3,4,5 andp1.2,1.5,1.8,1.95, using the literal
finite free convolution and exponent1/(p−1). None of12 runs found a negative
scale-free deficit; minima approached degenerate relative scales. No theorem
or structural extremizer refutation claimed. The script uses floating point;
near-zero samples are NOT certificates. Files:screen_pstam.py,pstam-screen.json.
PDFSHA c973fa5234a44c71f7b9316217bff02b6b35f8b5f766434371e0ea86d138f329.

373403 typeB Poincaré polynomial: actual2603.01956v1 Conjecture4.13 is open,
but source already reports a check throughn300. Do not repeat the same finite
screen as a discovery. Actual2026 successor2610.03138 fetched as companion;
its full mathematical body not read, no novelty inference made.

375854 GKP eventual real-rootedness: actual2607.06578v1 Intro/Theorem1.3 and
Section6 conjecture pp18–19 read. Real-rooted auxiliaryP case is already
proved. A symmetry/lattice-assumption transcription issue could yield only
an old-mechanism/wording correction and is not pursued as new discovery.
No substantive general complex-P result established.

## New candidate separated from screening

A continuous branch-switching cubic inC([0,1],C) potentially refutes the
C*-algebraic Sendov conjecture while retaining completely split derivative,
strict interior roots/critical roots, and positive continuous convex weights.
Full hand proof and exact checks are in siblingparent-sendov/. It is credit0,
needs independent source/math/novelty review and full Lean/paper/packet.


## Additional exact-source screening: reciprocal subsums and q-Pythagorean triples

374663: actual latest2605.10512 PDF read for definitions, Proposition3.8,
Conjecture4, and final Remark11. Actual companion2605.21718 read for its theorem
statements/status table. The six coprimality and special-value/recurrence questions
explicitly resolved there are excluded; no re-formalization is pursued. The
ordinary denominator log-concavity conjecture remains open. Exact Python-integer
DP through n300 checked6,059,604 inequalities; failures were exactly the stated
n3,5,6,7. No unexpected failure and no universal proof. See screen_subsum.py and
subsum-screen.json. LatestsourceSHA539aea158d7f1960e38f6087aacd12b7b7fdd64038d8826b627b2e23fbe2a7e4,
companionSHA6593c03b6fb85a09c8e5d5a6a4f9a8f9b71d000ad394d1b2ce9292eafc8dae67.

373286: actual2602.20536 formulas12,14,17-19 and unimodality conjecture read.
Exact q-rational matrix-word search tested42,767 triples: all binary construction
words through length16 and10,000 random words of length17–100, with exact checks
against all three Euclidean values at q1 and coefficient nonnegativity. No
unimodality counterexample. An initial NumPy-padding fixed-width contamination
was caught by the q1 identity assertions; replaced padding by genuine Python
integer construction and replayed the complete search with warnings as errors.
Final successful results use arbitrary-precision integer object arrays. Finite
screening is not a discovery or universal proof. See screen_pythagorean.py and
pythagorean-screen.json. SourceSHA51ee8454a7b9e96b92ab6f973760ebf04a44d0101b713b6a29838bfcd435b941.

367933: latest2504.06197v2 actualSection3.1 has Conjecture3.6, but Theorem3.7
already proves all d1,2,3. Those cases are excluded. Even-d inner products use a
modified involution, as explicitly stated in the source; the naive density-only
paraphrase omits this. No general higher-d result or counterexample obtained.
SourceSHAcd870157b22df765f2cdb4d297dc68b797c846cba9f1258551c28e21c0ce8e3f.

372352: actual2512.24535v1 Conjecture4.5.1p35 visually inspected. A prospective
complete argument via cyclic compression of the source's mixed-tail Gram pencils
is now written in lanes/parent-kadar-yu/PROOF.md. This is not yet reviewed or
formalized and remains credit0. The potentially decisive identification uses
Proposition3.25 andEq3.2.17, not the conjectured explicit partition formulas.
The k=-1 boundary and both asymptotic clauses are explicitly addressed. MathDB's
companion grouping is misleading: actual1601.04382 is Tran's general rational
GF root-distribution paper and1510.01758 is Kelley–Owen on finite-field trinomials,
not earlier statements of the Kadar–Yu conjecture. The classical generic Jacobi
machinery is not itself new credit. SourceSHA2d6f180bf33021ca6ab819928dfe51c91d44bed2eba8ccf03d2e443ed6bf5c86.

## Prior-proof exclusions confirmed during renewed screening

372393: actual source2601.00916v4 Conjecture5.5 is already proved in Brandon
Deonarine, *Nested Violation Sets for the Generalized Damascus Inequality*,
10August2026, Theorem1. The actual primary PDF was read, including the reciprocal
identity, sign-pattern argument, symmetric Laurent-sum multiplier, and the
stronger strict improvement S_(n+1)>S_n>0. Its linked public Lean repository is
https://github.com/M3RCU3Y/damascus-inequality-nestedness . The parent's independent
multiplier derivation reproduces this already public mechanism and is uncounted.
Primary https://brandondeonarine.com/papers/nested-violation-sets.pdf
PDFSHA e7b1d931653ddda947b8fdb2d4d86edf1effc212479092f8fd75a77f4118877f . The live MathDB open status is not novelty evidence.

369283: already excluded in the ledger. Actual2610.12063v1 Corollary3.2 explicitly
proves the entire source conjecture using Guillot–Khare–Rajaratnam's entrywise
power superadditivity theorem. The parent independently found the same Gram-matrix
argument, then checked the exclusion before formalization. No new credit.

335919: the average absolute Rademacher inner-product constant1/sqrt2 is the
classical sharp Khintchine constant, not a fresh discovery. No credit pursued.

322914/324064: actual Audenaert1410.4941 Theorem1 and introduction read. The
primary explicitly states that it solves Miao's conjecture, in the stronger form
with arbitrary increasing index selections. Both initial-segment MathDB versions
are excluded. PDFSHA d6611d8add448b1ceaf3c75b5875e118d05d278f4bdc10a5da132ac239f399c8.

324172: actual Li--Sze author-hosted *Determinantal and Eigenvalue Inequalities*,
Corollaries2.6/2.7 and their derivation read. Corollary2.7 explicitly proves the
exact sharp factor2^m for every accretive-dissipative matrix. Excluded. Primary
https://cklixx.people.wm.edu/Fischer-final.pdf , PDFSHA
48cf353b275adece929c665290f5bf978f5d6360b83bab85d38dce98bbf9c21b.

341578: Speyer2022 actual paper's Theorem2 proves diagonalizability and the
conjectured multiplicities as LOWER BOUNDS. Exactness and absence of other
repeated eigenvalues are not asserted as proved. Do not conflate this substantial
partial resolution with the full source statement; no new result obtained here.

362175: actual Pang2610.29240 introduction/Theorem1.1 read. It solves the sharp
UNWEIGHTED-output RANK-ONE problem, a distinct restriction of the general weighted
commutator problem, citing Fang--Cheng2025. Those known rank-one constants are
uncredited; no full general-matrix resolution inferred.

372794: full live MathDB solution46acd5c9-9ae6-4584-a626-588caaf59c7b read.
Shivam Patel posted the complete positive generating-function proof on20August2026;
the parent independently checked its common-denominator identity by exact SymPy.
Excluded. Open status does not override an existing posted proof.

330122: actual Shapiro1503.05295 Conjecture12 formula read, matching the literal
MathDB claim. The quadratic x²+1 has no real roots and G1=-4, so the statement
has an elementary quadratic-discriminant defect. The power family
p=(x²+1)^m also has G1=-4m²(x²+1)^(2m-2)<0. These are not pursued or counted
as substantive discoveries under the campaign's strict standard. The2023
preprint on Shapiro's12th conjecture was retrieved for future context checking;
its mathematical body has not yet been assessed, and no novelty inference is made.

364455: actual source2408.12386 advertises a disproof of the Fischer--Kubitzke
conjecture; the2026 Transactions record agrees. Its full counterexample body
has not yet been read here, so no formal resolution credit or new work is pursued.
