# T117Q contribution and eligibility review, round 1

Role: independent contribution/eligibility gate (Factory Opus 5.5). Correctness of the
final candidate is ASSUMED for this gate only; the separate proof gate decides it. No
acceptance, count, ledger, staging, commit, upload or publication action is taken here.
I did not read the parallel proof reviewer's draft or directory.

## Verdict

**SUBSTANTIAL** (conditional on an independent full-scope proof PASS).

The dimension-uniform spectral chart selection of candidate §§1–3 is a genuine new
bridge, not a robust norm-only transfer of the source. The source's L1 contraction
bound depends at its final step on scalar coordinate decoupling and a sphere-net
majority-chart lemma. Neither is available for trace-class targets of unbounded
dimension. The candidate replaces that step by an operator-order selection argument
that the source does not contain, and the resulting statement (near-sqrt(log n)
uniform average distortion of genuine negative-type metrics into S_1(H) for every H)
is not given by any operative antecedent I read. Literature novelty is NOT demonstrated:
the search was bounded (see reading-and-search-limits.md), and the bridge is a short
combination of standard operator tools. The classification is new-to-project
substantial, with bounded literature coverage.

Required positioning items RQ1–RQ4 below do not change the verdict, but they must be
satisfied by any later manuscript or acceptance record.

## Inputs authenticated

- Author MANIFEST.json SHA256 equals the external anchor
  053986e5a446cd18251b3e3e8b917bc58cafb0f68d6de87562fe190766e28ae2 (original and the
  /var/tmp copy). candidate.md, original-scope.txt and checkpoint.md also match their
  external anchors. The author verifier passes with the anchor (52 payloads, 12
  directories) and fails with a wrong anchor.
- All 20 source blobs were independently recomputed as Git blob SHA-1 and compared with
  the complete canonical sources/preprints-tree.json (SHA256 eeecc1da…dc5e09b, 13223
  entries, truncated=false), not with the author's selected receipts: 20/20 match path,
  type and blob id. These are all tex/bib blobs of both catalogue-117 directories; the
  two PDFs and READMEs are not copied.
- Details and replays: replay-record.json. No checksum is mathematical or novelty
  evidence.

## Frozen scope and chronology

The candidate's statement preserves the full frozen scope: every complex Hilbert space H
(including nonseparable), every 1-Lipschitz F into S_1(H), ordered uniform-pair averages,
genuine metrics (positive on distinct points, all triangles) that are squared Hilbert
distances, and exponent 9/2. The weighted first-chart measure is converted to exactly
uniform copies (§6), and an equilateral zeta term restores strict positivity. No
bounded-dimension, commutative, weighted-only or weaker-exponent replacement is used.

Chronology was checked in actual Git history, not only in author prose. T3 checkpoint
commit e58f6a4e (2026-10-18 03:09:02 -0700) already contains original-scope.txt with
the final blob 4992564a (SHA256 fc5a8f87…fe36). That checkpoint has no candidate.md; the
first candidate.md appears in c67116d6 (03:21:54). The checkpoint versions of
matrix-selection-derivation.md and working-interface.md differ from the final ones only
by the added "Historical pre-freeze working note" header. So the scope did precede the
full proof assembly. It did NOT precede the method: the pre-freeze derivation already
contains the operator Wick bound, the scalar moment design, the spectral selector,
the positive pairing and the prospective (log log n)^(9/2) exponent. The target is
therefore method-shaped (self-posed exponent), which the author discloses. This is a
limitation on the importance argument, not an eligibility failure.

## Source-family eligibility

Catalogue family 117 has exactly two pinned directories (checked in the complete tree).
My own search of authored campaign/iteration/experiment notes (private bodies, inputs,
snapshots and literature directories excluded; r59 and t117q-* excluded) found no
developed family-117 chain: the only family-titled hits are keyword matches inside the
unrelated I14 spectral-width corpus scan. The r54 negative-type notes concern family 174.
The hardness companion (source117-2) proves NP-hardness of constant-factor uniform
sparsest cut (main.tex abstract; sections/00-introduction.tex Theorem thm:main, read)
and has no metric-embedding or trace-class statement. A keyword screen of all 9340
pinned tex/bib/md/txt blobs (each re-verified against the canonical tree) found no
pinned manuscript that combines Schatten/trace-class/nuclear-norm terms with
negative-type, sparsest-cut, average-distortion or bi-Lipschitz terms, apart from three
physics papers whose hits are unrelated ("trace class" operators and fixed bi-Lipschitz
reparametrizations). Eligible.

## Operation-level comparison

| Op | Candidate operation | Antecedent and status |
|---|---|---|
| O1 | Lemma 1: E(sum g_j X_j)^(2q) <= (2q-1)!! I when sum X_j^2 <= I, via register contractions | Standard operator-valued Wick/Khintchine phenomenon; paid tool. Not credited as the contribution (author agrees). |
| O2 | §2: one finite family of SN = m^(10q+6) directions satisfying the averaged moment bound (2.1) for every selfadjoint tuple of every dimension, by matching scalar monomial coefficients | Standard design/derandomization technique. New to the source; enabling, not by itself substantial. |
| O3 | §3 Lemma 2: X_j = E[g_j sign(A(g))] gives sum X_j^2 <= I and Y = sum A_j X_j = E|A(g)| >= 0; operator concavity gives S^-1 sum_s Q_s <= C q/m; Loewner Markov gives spectral projections P_s with sum_s P_s >= S/2 and ||Z_si P_s||^2 <= h; positivity of Y lets Tr Y be averaged over NONCOMMUTING P_s | **Unpaid bridge.** Replaces the source's component-wise good-chart choice (contraction.tex lines 231–279) and its sphere-net majority lemma (directions.tex item 3; directions-proof.tex lines 196–220). No read antecedent performs it. |
| O4 | §4: S = m^(10q) charts, epsilon = m^-200/S, tau = m^-2000/S^2, vertex count exp(Cm(log m)^2) | Source formulas already carry explicit S-dependence (kernel.tex lines 51, 83, 167–169, 197). Technical bookkeeping. Note the source calls fixed powers of m "essential for the vertex count" (kernel.tex line 22); the candidate pays that with exponent 3 -> 9/2. |
| O5 | §5: trace-norm smoothing, coarea jump representation, Banach Gaussian-rotation Poincaré, Hermitian dilation | Norm-only transfer of paid source steps (contraction.tex lines 94–229) plus the Maurey–Pisier argument the source already cites. Routine. |
| O6 | §6: uniform copies plus an equilateral zeta to get a genuine metric | Routine variant of reduction.tex lines 109–198. |
| O7 | §7: finite-rank compression for arbitrary H | Standard. |

### Why O3 is not routine robust transfer

The source contraction bound is stated and proved only for l_1^D. Its last step sums
inequality (con:eq:good-chart-average) over scalar components alpha, each with its own
alpha- and theta-dependent good charts. The source introduction stresses this (main.tex
lines 281–284). In S_1 there are no decoupled components. The relevant "direction" is a
matrix tuple with sum X_j^2 <= I in arbitrary dimension, so the source's 1/m-net with
independence across charts has no analogue. I checked the natural shortcuts:

1. One chart plus type 2. S_1 has no dimension-free type-2 constant, so a single chart
   gives only the trivial N t bound and loses the needed sqrt(q/m) factor.
2. Eigenvector-wise Hilbert-valued good charts. For each eigenvector e_k of Y one can
   control |Z_si e_k| on half the charts with the source's own S (a net over trace-one
   PSD m-by-m matrices is affordable). But this fails twice. sum_k |b e_k| over an
   orthonormal basis is not bounded by ||b||_1 (rank one b = x y* gives up to
   sqrt(D)|x||y|). Columnwise bounds on Z_si e_k also do not control ||Z_si P|| for the
   resulting projection P. An operator-order selection with a positive pairing is
   genuinely needed.
3. Composition with Kush–Nikolov–Tang. Their Theorem 34 (arXiv v1, extracted lines
   1650–1655) gives a constant-average-distortion embedding of the p/2 SNOWFLAKE of
   Schatten-p into l_2. At p = 1, composing with F only shows that a map of (V, sqrt d)
   into l_2 is 1-Lipschitz. Since sqrt d is already Euclidean, this gives no obstruction.
   A Lipschitz constant-average-distortion map from finite subsets of S_1 into L_1 would
   make T117Q a routine corollary of the source (with exponent 3). No such theorem was
   found.
4. Luo–Wang–Zhou Theorem 1.1. It bounds the cube average by sum_j ||∂_j f||_{L1, psi}
   (an l_1 sum of coordinate Orlicz increments). It has no Gaussian cancellation, so it
   cannot give the needed bound E||sum g_j A_j||_1 <= C sqrt(m) polylog(m) from chart
   representations. The candidate's local bound is a different inequality.
5. Cordero-Erausquin–Eskenazis Theorem 13 with Luo–Wang–Zhou. Together they give S_1
   distortion lower bounds for nonlinear cube quotients C_n/R with small geometric
   influences. That route needs a quotient metric of negative type with small influences,
   which is not supplied by any source I read. Its gain is KKL-type, a log of inverse
   influences, i.e. at most of order log(dimension) = O(log log of the number of points),
   far below sqrt(log n). It is also bi-Lipschitz, not uniform-average. It does not reach
   T117Q.
6. Quantum expansion (Escudero Gutiérrez–Muguruza Theorem 1). It concerns compressed
   blocks of bistochastic tuples. The authors themselves say the resemblance to metric
   Poincaré inequalities for arbitrary maps is "notational, rather than operational"
   (Section 3.2). No arbitrary-map lower bound is inferred here from channel spectral
   gaps.

### Literature context (bounded)

- Naor–Pisier–Schechtman (arXiv 1710.08896) explain that ℓ_1 dimension-reduction
  arguments using coordinate sampling "seem to be inherently commutative and without a
  matricial interpretation". They recall as open whether the Heisenberg group
  bi-Lipschitz embeds into S_1 (extracted lines 292–319, 325–327).
- Naor–Young (arXiv 1701.00620) record that it is unknown whether H^3_Z embeds into S_1.
  They suspect a sqrt(log n) lower bound and say it "would be of great interest to devise
  an approach that applies to mappings that take value in S_1 rather than L_1(R)"
  (extracted lines 603–623, 880–883).
- Escudero Gutiérrez–Muguruza (arXiv 2405.03517, Section 3.2) pose the minimal n-point
  distortion into S_p as an open question and state that, to their knowledge, there is
  no literature on it.

These statements show that replacing L_1 cut/coordinate methods by S_1-valued arguments
is a recognized difficulty. T117Q does NOT resolve the Heisenberg question; it concerns a
different, source-built family of negative-type metrics. These citations support, but
do not establish, novelty.

## Required items (positioning; verdict unchanged)

- RQ1. Any manuscript must compare against Naor–Pisier–Schechtman 2018, Naor–Young 2018
  (the S_1 remarks above) and the Cordero-Erausquin–Eskenazis Theorem 13 + Luo–Wang–Zhou
  route. It must state why each does not already give the theorem (points 3–5 above or
  equivalent). The author's packet omits these comparators.
- RQ2. Novelty wording must stay "new to this project; no antecedent found in a bounded
  search". It must not say "first" or claim to answer the Naor–Young Heisenberg question
  or Escudero Gutiérrez–Muguruza Question 2.
- RQ3. Metric cotype of S_1 must be addressed. Jiao–Luo–Wu (arXiv 2610.21445, posted
  2026-10-15, three days before the candidate) prove sharp metric cotype 2 for S_1
  (Theorem 1.3). Their introduction (extracted lines 177–188) recalls the
  Giladi–Mendel–Naor question whether c_S1([floor(sqrt n)]^n_inf) >= c sqrt(n), i.e.
  bi-Lipschitz lower bounds of order about sqrt(log N / log log N) for N-point l_inf
  grids. So (a) any claimed consequence for general N-point S_1 distortion (for example
  Escudero Gutiérrez–Muguruza Question 2 at p = 1) must be checked against this cotype
  route, and (b) the manuscript must explain why sharp metric cotype 2 does not already
  give the negative-type, uniform-average, all-H statement. I did not read the
  Mendel–Naor or Giladi–Mendel–Naor bodies and did not test (b). A weak heuristic against
  (b): L_1 also has sharp metric cotype 2 (Cheng–Wang–Xiang, recalled at lines 189–190),
  yet the source needed a dedicated construction for L_1. This is not a proof. The
  distinctive content of T117Q is the negative-type, uniform-average, all-H statement.
- RQ4. The record must say plainly that the exponent 9/2 and S = m^(O(log m)) were
  selected by the method before the freeze (checkpoint evidence above). It must also say
  that, through the diagonal copy of l_1 in S_1, the theorem implies only an L_1
  average-distortion bound with exponent 9/2, weaker than the source's exponent 3. It
  does not supersede the source theorem.

## Optional editorial improvements

- E1. The candidate's Statement writes C(log log n)^(9/2)/sqrt(log n); the frozen scope
  writes c^-1. Harmonize.
- E2. Cite the operator-valued Gaussian Wick/Khintchine literature for Lemma 1 (for
  example Haagerup–Pisier or Buchholz type operator bounds) and the spherical-design
  literature for §2. Keep both as paid tools.
- E3. Rename the selector Q_s or the geometric Q_s^geom globally. The parenthetical
  disambiguation is easy to miss.
- E4. Tropp passages are browser-only, with no local identity. Either obtain an
  authenticated copy or present them as orientation, not evidence.
- E5. State the companion (source117-2) coverage as "keyword-screened, not read",
  consistently across candidate.md and primary-comparison.md (it already is in
  reading-limits.md).

## Diagnostics (not proof dependencies)

On a /var/tmp copy, after authenticating the copy against the external anchor, the
author's integrity controls passed all 13 cases with their expected reason substrings.
The scratch directory was inside the copy's checks/, and the canonical packet was never
used as scratch. The author's matrix_diagnostics.py was replayed with
/tmp/agvenv/bin/python (Python 3.14.7, NumPy 2.5.3), exit 0. Its JSON output is
identical to the recorded checks/matrix-diagnostics.json (372 pairing cases, 12 moment
cases). These finite floating-point checks do not establish the arbitrary-dimension or
all-size theorem and are not used in this verdict.

## Limits

Correctness is assumed for this gate. Literature novelty is not demonstrated. Exact
reads, searches and unread leads are in reading-and-search-limits.md. Newly retrieved
third-party bodies are under private/ and ignored by Git.

## Package

Members: review.md, reading-and-search-limits.md, replay-record.json, verify_review.py,
review_controls.py, controls-result.json, .gitignore, sealed by MANIFEST.json. The
Git-ignored private/ directory is excluded from membership. Verify with
`python3 verify_review.py verify <dir> --anchor <SHA256 of MANIFEST.json>`, taking the
anchor from the parent's record, never from this package. controls-result.json records
review_controls.py run on /var/tmp copies of the pre-final seal (the final seal adds
only that file); final positive and wrong-anchor checks are reported outside the package.
