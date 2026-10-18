# TREE097 independent contribution and eligibility review, round 1

Reviewer role: independent CONTRIBUTION/eligibility review only. Original
prose CC BY 4.0. The parallel proof review (tree097-proof-r1) was not opened
and did not influence this report. Proof correctness is assumed solely for
classification; proof-level remarks below are incidental and are not a proof
gate.

## Verdict

**TECHNICAL** for the full, unchanged original scope (TREE097, frozen
original-scope.txt SHA256
08338d40a730c126691accaaa60db530116b5df44393ca22d2c1663cc9099821).

No exact primary duplicate was found, so the verdict is not DUPLICATE. The
scope was frozen before a complete proof, is distinct from the unresolved r4
two-order target, and is properly quantified, so the verdict is not
INELIGIBLE. The reading was sufficient to compare every load-bearing
operation, so the verdict is not BLOCKED.

The reason, at operation level: the claimed increment (one hard-supported
all-prefix good set that hits every Gaussian-half body, then its
leaf-sensitive assembly) is a short combination of (i) a source-internal
generalization of the pinned slab-energy argument, (ii) an elementary energy
bound for Gaussian bodies, (iii) the DGLN finite-set duality applied exactly
as designed, (iv) the independent local-subgaussian path-summation
architecture already used by Russo–Wei, and (v) textbook heavy-path counting
and sphere nets. The resulting bound is non-sharp, and its improvement over
routine bounds is confined to the regime 1 << log L < d. Taken together this
does not meet the campaign substantiality bar.

## 1. Frozen-input authentication (identity only)

* Author packet `fresh-structural-discovery-r44/`. Before running it I read
  verify.py in full. It is read-only, requires a caller anchor, scans
  lstat with no symlink following, rejects hardlinks/nonregular nodes and
  nested manifests, checks exact file and directory inventory, the frozen
  scope hash, 51 Git blob identities and 8 primary pairs.
  `python3 -B verify.py --expected-manifest-sha256 ceb4d164...e572e` gave
  PASS: 90 payload files, 25 directories, 51 pinned blobs, 8 PDF/text pairs.
  An all-zero anchor was rejected with exit 1.
* The four anchored files match the brief: MANIFEST.json ceb4d164..., 
  candidate.md 7035c4b5..., original-scope.txt 08338d40...,
  prefix-law.md baa4071a....
* Independent recomputation: for all 51 selected source bodies I computed
  the Git blob SHA1 from the bytes and matched each against the COMPLETE
  `sources/preprints-tree.json` (SHA256 eeecc1da...e09b, truncated=false,
  13,223 entries), not merely against the packet's receipts. 51/51 matched.
* All eight primary PDF and text SHA256 values were recomputed and match
  primary-receipts.json.
* assembly-author-support.md equals
  tree-signing-assembly-r1/assembly-proof.md (SHA256 4f3e4b2a...), and that
  packet's manifest.json has the recorded external anchor a4e51344....

These are identity checks only. No checksum establishes mathematics or
novelty.

## 2. Original-scope coverage

The theorem reviewed is exactly the frozen statement: an absolute C; every
d>=1; every finite nonempty rooted tree with L leaves; arbitrary unit-ball
vertex labels in R^d (zeros and repetitions allowed); one signing; every
root-to-vertex sum including both endpoints bounded by C sqrt(d log(1+L));
C independent of N, depth, unary lengths, degrees and labels; empty tree and
d=0 trivial; existential and offline; no algorithmic or sharpness claim.

* The candidate (sections 3–7) addresses all of these quantifiers. The two
  regimes are combined by an existential case split on (d,L). d=1 is covered
  by greedy signing and the d=0/empty cases by zero sums.
* I found no narrowing, relabeling or substitution. The r4 target T2 (one
  signing for two arbitrary orders of the same indices, bound C sqrt d) was
  checked in `fresh-structural-discovery-r4/candidate.md` lines 1–60. The tree
  statement gives disjoint vertices distinct signs. It is a different
  incidence system, and the candidate correctly leaves T2 unresolved.
* The chronology is disclosed. The scope was frozen after exploratory
  local-law and heavy-light ideas and before the complete proof. This is
  eligible. It bears on significance (objection R4), not on eligibility.
* The classification covers the whole package: the local law, the
  heavy-light assembly, the unary-compression regime and the regime split.
  No sub-part is separately classified as substantial.

## 3. Operation-level comparison with actual source and primary text

| # | Operation in the candidate | Where it is already paid | Assessment |
|---|---|---|---|
| A | Filtered body D, predictor rows m_i, column bound ‖Me_j‖^2<=sigma^2, K_0=(2D_*D) intersected with slabs, energy <= kappa^2 trQ/2 | pinned 097 assembly.tex prop:filtered, lem:slab-energy, eqs. predictor-columns/application-energy | Verbatim source, with the constant halved. |
| B | Intersection subadditivity lambda_Q(D∩E) <= lambda_Q(D)+lambda_Q(E) | pinned 097 brownian.tex proof of lem:slab-energy: Brownian survival rate plus path Gaussian correlation applied to the closed sets closure(D_*D) and half-slabs | Same proof with a general symmetric body in place of a slab. Routine generalization inside the source. |
| C | Gaussian-half body K has lambda_Q(3 int K) <= H_G trQ | Not stated in the source. The energy class replacing Banaszczyk's measure class is the framework of GFL/Bandeira (lead only, see limits) | Elementary half-page test-function estimate (phi = distance cutoff times sqrt of the Gaussian density). Correct as written and technical. |
| D | Apply prop:adaptive to K_0∩E with clipped predictor shifts. Clipping is inactive at the end, and exact cancellation R_i x = sigma Σ eps_j v_j | pinned 097 assembly.tex proof of thm:signing, "Choosing the coefficients"/"Cancellation" | Verbatim source argument run on a smaller body. prop:adaptive is stated for any body satisfying the energy bound. |
| E | A_good meets cB for every Gaussian-half symmetric B, hence a c_0-subgaussian law on A_good | DGLN 2019 Thm 1.2 (lines ~238–298) for an ARBITRARY finite T ⊂ R^n. KRR Thm 19 uses the same "Banaszczyk-type hitting ⇒ subgaussian law" principle via cloning, crediting Meka and Nikolov's path case | Direct application of a tool built for exactly this purpose. The only input is the hitting property from B–D. |
| F | Pull back by R_i with R_iR_i^T=I, so fixed-prefix marginals are O(1)-subgaussian. Symmetrize, then convert tail to MGF | Elementary | Bookkeeping. |
| G | Heavy-path decomposition: L chains, at most log2 L light edges | Sleator–Tarjan heavy-path decomposition (standard) | Textbook. |
| H | Independent whole-chain samples. Each chain-head state is a sum of at most log2 L independent fixed-prefix subgaussian terms; Chernoff plus a union over L heads × 5^d net gives O(sqrt(d log L)+log L) | Russo–Wei 2610.16715v1 Thm 2.1(ii): independent local signers whose errors add along a boundary path of length <= log T. Conditional subgaussian summation plus union gives O(log T + sqrt(log T (d+log 1/δ))), the SAME shape | The architecture is paid. The only new point is that the union bound counts chain heads rather than all vertices, because inside each chain the hard bound holds surely. That is a one-line consequence of the local law. |
| I | Unary-chain compression, source097 on each chain, Bansal et al. Lemma 4.1 on the compressed tree, giving O(d+sqrt(d log L)) | Bansal–Jiang–Meka–Singla–Sinha 2111.07049v1 Lemma 4.1 (full proof, lines 888–982). KRR Thm 15 is the same edge-labelled tree lemma | Routine. The author concedes this. |
| J | Regime split at log(1+L) versus d | Arithmetic | Bookkeeping. |

The genuinely new statements are therefore (1) the hard-supported
subgaussian prefix law (A–F) and (2) its use in H to make the union bound
independent of N. I assess each below.

### 3.1 The hard-supported prefix law

This law is a stronger statement than the stipulated source theorem, and I
found it stated in none of the primaries read. KRR Thm 1/19, Aden-Ali Thm 1/2
and the path case attributed to Nikolov give subgaussian prefix laws without
a length-independent sure bound. Source097 gives a sure bound without a law.
However, the proof needs no idea beyond the source:

* The source's operative proposition prop:adaptive already applies to every
  bounded open symmetric convex body with lambda_Q <= kappa^2 trQ. The source
  itself builds its body by intersecting a filtered body with slabs and pays
  for the intersection by Brownian survival and Gaussian correlation (B).
  Replacing "slab" by "any symmetric convex body of bounded energy" is the
  same argument.
* A Gaussian-half body has bounded diagonal energy after a fixed dilation (C).
  This is a short computation and the natural first check for anyone using
  the energy class in place of Banaszczyk's measure class.
* Once a finite set hits every Gaussian-half body, DGLN Thm 1.2 converts this
  into a subgaussian law on that set. DGLN state it for arbitrary finite T
  precisely so that such restricted sets can be used. KRR section 5 shows the
  same "Banaszczyk-type hitting ⇒ distribution" move is standard for prefix
  and tree settings.

An expert who knows the source and DGLN would reach the law by the route
"the source argument is robust under intersection with a Gaussian body, so
apply DGLN". The pieces fit without a new mechanism.

### 3.2 The leaf-sensitive assembly

Heavy-light counting, independence across chains, MGF multiplication and a
5^d net with a union bound are standard. Russo–Wei Thm 2.1(ii) already uses
independent local subgaussian signers summed along a logarithmic-depth path,
with a union bound, and obtains the same O(log + sqrt(d·log)) form. The
internal-prefix observation (a path exits a heavy chain at an internal
vertex, so fixed-prefix rather than terminal marginals are needed) is
correct and necessary. It is a careful check, not a new operation. The
local law was formulated to supply exactly this.

### 3.3 Quantitative significance

* Known lower benchmarks (actual primary text): Ω(sqrt d) for paths (basis
  vectors; source097 introduction) and Ω(sqrt(log T)) for a complete binary
  tree in R^2 (Bansal et al. Thm 1.5, proof lines 1119–1137). With L about
  T/2 leaves this is Ω(sqrt(log L)) in every d>=2.
* Fixed d: the routine route I already gives O(d + sqrt(d log L)) =
  O_d(sqrt(log L)), which matches the lower bound. The candidate adds nothing
  to the fixed-d order.
* log L >= d: the candidate uses the routine route I.
* log L < d: the candidate improves min{O(d), O(sqrt(d) log L)} among
  N-independent bounds, and O(sqrt d + sqrt(log N)) when N is only moderately
  large, to O(sqrt(d log L)). It still leaves a gap of up to sqrt(log L)
  against the lower benchmark max{sqrt d, sqrt(log L)}. The candidate
  correctly claims no sharpness.
* The natural benchmark target, O(sqrt d + sqrt(log L)), interpolates the
  path theorem and the binary-tree lower bound. The candidate neither reaches
  it nor determines the true order in any new regime. The product form
  sqrt(d log L) is exactly what the assembly yields.
* Bansal et al. section 6 (lines 1276–1333) poses no tree leaf-count
  question. The result does not answer a posed problem in the primaries read.

## 4. Objections

### Required

**R1 (contribution, decisive).** The local hard-supported law should be
classified as a technical source-internal upgrade (operations A–F), not as a
new mechanism. Intersection subadditivity is the source's own slab-lemma
proof with a general body. The Gaussian-body energy bound is an elementary
estimate. The subgaussian law is DGLN Thm 1.2 applied to a finite set, which
is exactly its stated scope. Any manuscript must present the law that way.

**R2 (contribution, decisive).** The assembly (G–H) must credit Russo–Wei
2610.16715v1 Thm 2.1(ii) as a direct architectural antecedent: independent
local subgaussian contributions along a logarithmic-depth path with a union
bound, giving the same O(log + sqrt(d·log)) form. It must also credit
heavy-path decomposition as classical. The candidate's §8 sentence ("That
path-summation architecture is prior") is accurate. The leaf-count saving
must be described as a consequence of the law's sure bound, not as an
independent operation.

**R3 (attribution, missing comparator).** candidate.md does not state the
primary tree lower bound, Bansal et al. 2111.07049v1 Thm 1.5 (Ω(sqrt(log T))
on a complete binary tree in R^2). That lower bound is needed to state the
regime picture honestly: the fixed-d leaf dependence is already sharp by
routine means, and the new bound is non-sharp where it improves. The author
reading log cites ITCS lines 1020–1150, which include this proof, but the
candidate does not use it. Any manuscript must add it together with the
explicit comparison in §3.3.

**R4 (significance framing).** The result must not be advertised as
determining tree prefix discrepancy, answering a posed question, or
"completing all d,L regimes" in any sense beyond the stated non-sharp upper
bound. Half of the claimed all-regime statement (log L >= d) is the routine
route I. The improvement is confined to 1 << log L < d. The target's shape
was chosen after the exploratory assembly was known, which the scope
discloses.

These required items do not change the verdict. They describe the correct
attribution if the material is retained as technical research. They are not
a repair path to SUBSTANTIAL, and no narrowing or relabeling would change
the classification.

### Optional

**O1.** Section 5 of prefix-law.md (the whole sign vector is O(1)-subgaussian
via the orthogonal block map) is a stronger, cleaner form of the law. It
should be kept clearly marked unused and unclaimed, as the author does. It
does not alter the classification.

**O2.** In candidate §2 ("gives a B_2 contained in K"), write a·B_2 ⊂ K
explicitly: support function h_K(θ) >= a, hence aB_2 ⊂ K, hence
K + aB_2 ⊂ 2K. As written the scalar a can be misread as an article.

**O3.** In candidate §6 the Bansal et al. lemma is invoked for "every
symmetric convex K with measure >= 1-1/(2m)". The actual Lemma 4.1 statement
says "any convex body K" (line 888ff). The candidate uses only Euclidean
balls, and the proof's root step uses symmetry, so nothing breaks. Quote the
statement as written.

**O4.** reading-and-limits.md should say that the
bansal-et-al2022 extent includes Thm 5 (ITCS numbering, the tree lower
bound). It should also say that KRR Thm 19's own text credits an unpublished
Nikolov manuscript for the path case of a subgaussian prefix law and a Meka
argument. Both are relevant attribution leads.

### Incidental proof-level remarks (not a proof gate)

While classifying I checked the following by hand and found no gap:
intersection subadditivity via closure(aD) ⊂ D for a<1; the Gaussian-body
energy constant 6/a^2+3/2; unclipping; R_iR_i^T=I pull-back; the moment and
MGF conversion (2e^x-1 <= e^{2x}); the Chernoff/net union count
L·5^d·exp(-(d log 5+log 2L)) = 1/2; the compressed-tree identity using
complete ancestor endpoints; and the regime arithmetic. This is not a full
audit. In particular I did not re-derive DGLN's minimax direction or the
source's analytic propositions (both stipulated or primary).

## 5. Search and duplicate assessment

Bounded web searches on 2026-10-17 (queries recorded in reading-limits.md)
found no statement of a leaf-count-only tree bound or of a hard-supported
subgaussian prefix law. Neither did the pinned catalogue (749 preprint
directories, keyword screen of names; CONTENTS entry 097) nor the campaign
history (rg, excluding private copies and the parallel proof review). Absence
from bounded searches is not evidence of worldwide priority. DUPLICATE is
not asserted. TECHNICAL rests on the operation comparison above, not on any
missing theorem text.

## 6. Final classification

TECHNICAL: complete-scope, assumed-correct, eligible research that
introduces no operation beyond credited source, primary and textbook
mechanisms. Its quantitative gain is non-sharp and confined to one regime.
No count increment is supported by this review. The campaign remains at
13/20 as far as this gate is concerned. Acceptance is the parent's decision.
