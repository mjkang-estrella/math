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
