# Source and primary reading ledger

Author: Myeongjin Kang. CC BY 4.0. Downloaded is not synonymous with read.
These are author-side comparisons, not an independent gate.

## Pinned identities and operative passages

Pin: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, repository openai/math.
source-receipts.json gives exact pinned raw URLs, Git blob hashes and SHA256
for all 33 non-PDF blobs of both family-080 companions. Comparison against
the canonical complete tree shows only the two paper.pdf files omitted.
All acquired source bodies are under ignored private/preprints/. The
canonical complete tree and upstream descriptor are under private/context/.

Higher-dimensional directory:
Endpoint-pointwise-convergence-for-the-Schrodinger-equation-in-higher-dimensions-September-24-2026.
Under build/sections/ this round read:

- introduction.tex, all 187 lines;
- weak.tex, all 154 lines, including w:weak, but not its included angular,
  wall and flattening proof bodies;
- fractal.tex, lines 1–240 of 631, including d:measure and its actual
  n-dimensional growth/native-time/tube-moment hypotheses;
- endpoint.tex, lines 1–440 of 496, including full compact-layer reduction,
  e:short-time, e:dual-square, e:maximal, Gaussian approximation lemma and
  the opening of the final representative argument.

Planar directory:
Endpoint-convergence-for-the-planar-Schrodinger-equation-September-24-2026.
Read build/sections/01-introduction.tex, all 148 lines, and
09-endpoint.tex, lines 1–480 of 715. The latter includes the full proof of
prop:shortmax, lem:endpoint-time-separation, lem:endpoint-localized-dual,
lem:endpoint-square-sum, and thm:maximal's statement. Its later completion
and Gaussian-limit discussion were not read in this round. No reading of
the other planar proof sections or included figure bodies is claimed.

The scalar deduction uses exactly those read short-time/kernel/tree
interfaces, accepting their premises. It does not audit upstream proofs.
The independent input below the weak estimate is not reproved.

## Primary bodies

primary-receipts.json binds each PDF and its pdftotext -layout extraction.
version-receipts.json binds the three unversioned arXiv abstract pages
retrieved in this round; they list the used v1 versions. The Du–Zhang body
is the published Annals PDF. This is a bounded comparison, not an exhaustive
survey of every later result.

1. Bez, Kinoshita, Shiraki, *Boundary Strichartz estimates and pointwise
   convergence for orthonormal systems*, arXiv:2306.14536v1.
   URL: https://arxiv.org/pdf/2306.14536v1 . Read extracted lines 1–600 and
   1220–2000. In particular: Theorems 1.2, 2.1, 2.2; §6.1 finite-rank
   approximation; §6.2 kernel estimates and Schatten summation; §6.3 both
   necessary-condition constructions. Sections 3–5 as a whole were not
   read; only the tail preceding §6 was included. The operative comparison
   is the s≥n/4 maximal-in-time density proof, not its maximal-in-space
   Strichartz theorem. Its precise frequency loss is in
   orthogonality-interface.md §3. No conclusion is borrowed from a snippet.

2. Du, Zhang, *Sharp L² estimates of the Schrödinger maximal function in
   higher dimensions*, Annals of Mathematics 189 (2019), 837–861.
   URL: https://annals.math.princeton.edu/wp-content/uploads/annals-v189-n3-p04-s.pdf .
   Read extracted lines 1–170 only: introduction, Theorems 1.1–1.3,
   Remark 1.4, (1.6)–(1.7), Theorem 1.6 statement. The proof body is unread.
   Used only to guard against silently upgrading the output p to
   2(n+1)/n in higher dimensions. I66's read of another version is not
   attributed to this agent as a present read.

3. Hadama, Toyoshima, *Endpoint orthonormal Strichartz estimates*,
   arXiv:2608.21823v1. URL: https://arxiv.org/pdf/2608.21823v1 .
   Read extracted lines 1–235, 380–535, 756–970. This includes Assumptions
   1.2–1.3, Theorem 1.4, the key-ideas discussion up to its final assembly
   paragraph, the full Lemma 4.2 far-part proof, and Lemmas 4.4–4.5 with
   their proofs. Reading stops in Lemma 4.6's proof. The final spectral-band
   estimates, eigenvalue-counting proof and remaining applications were
   not read. The claimed obstruction concerns only the explicit product-
   measure |I| estimate, whose proof was read fully. The two-paper
   download/extraction call for items 3–4 printed font-mismatch warnings but
   succeeded; the displayed formulas used here were legible in the extraction.

4. Bhimani, Choudhary, *Pointwise convergence for single-particle Schrödinger
   equation and Schrödinger equation with infinitely many particles on the
   torus and waveguide manifolds*, arXiv:2609.15363v1.
   URL: https://arxiv.org/pdf/2609.15363v1 . Only extracted lines 428–440
   and 500–540 were read, plus locator searches. These are Corollary 1.11,
   the cited Euclidean comparison, and the authors' explicit description
   that the necessary condition uses a rank-one embedding. The proof is
   unread. This check merely prevents confusing a rank-one regularity
   obstruction with an orthogonality-sensitive one; it is not a premise.

## Operation assessment

Source weak short-time estimate: inherited substantial input.
Spatial localization, common-time-tree and convexity deficit: inherited.
L^q mass, Young inequality and duality: technical modification, not nominee.
BKS finite-rank density passage: existing operation; not claimed new.
Finite Schatten estimate for arbitrary critical graphs: unpaid/unproved.
Hadama–Toyoshima product-measure spectral method: existing, but its explicit
near-block time-length factor is unavailable for atomic graph time laws.
No source or primary is asserted to rule out the full density problem.

No full formalization was attempted. A meaningful later Lean effort could
formalize the finite weighted-tree telescoping and exponent identities, but
would certify only technical support. The unresolved Schatten bridge must
be proved analytically before a formal gate is proposed. Numerical checks
and integrity controls below cannot supply that proof.
