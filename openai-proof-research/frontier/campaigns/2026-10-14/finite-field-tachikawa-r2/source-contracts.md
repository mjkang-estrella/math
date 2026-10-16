# Source contracts and actual reading extents

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.
Third-party files are private reading copies with their existing rights retained.
Authentication, catalogue parsing, and semantic reading are different operations.

## Fixed upstream and fixed prior history

The accepted upstream revision is openai/math
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. The actual main theorem is accepted
as instructed. No attempt was made to audit its truth. The current upstream.json
was read. The complete preprints-tree.json was parsed (13223 entries,
truncated=false), and all seven referenced Git blob identities were matched.
The family-199 catalogue entries were read; the catalogue was not surveyed
again for a new family in this focused continuation. The original full catalogue
and tree snapshots remain in the authenticated r14 package, avoiding redundant
large copies. Historical screening claims belong to that fixed package.

Before reliance, r14's seal.json bytes were independently matched to external
SHA256 88428e36011c09d7920f4ebf36da39511af77f1bd770220d3f0ce49df02ee6d2.
Its manifests, their 46 payload records, three metadata files, exact inferred
directories, sizes and hashes were checked. No historical code was run.
inputs/r14-authentication.json records its exact 49-file tree. The user-supplied
full findings and parent assessment were read in the brief; the authenticated
candidate, checkpoint and source-contract bytes are the fixed historical
references. No prior partial reading is silently upgraded to full primary reading.

All seven TeX references below are at
preprints/A-counterexample-to-Tachikawas-second-conjecture-September-23-2026/build/sections/
under the pinned commit. Their actual retained files are referenced, not copied,
inside the authenticated r14 tree. Full paths, sizes, SHA256 and Git blob SHA1
are in inputs/pinned-references.json. Each Git identity was independently checked
as SHA1 of `blob <length> NUL <bytes>`, as well as against the complete tree.
A raw URL is obtained by prefixing the pinned path with
https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/.

- introduction.tex, blob 1c1c4f98074f32148f5077da2865ebc23203b55e:
  lines 1-175 read this round. Includes actual thm:main, the field, related
  results and construction through the evaluated-lift requirement. It gives
  the generic input only. Later field-extension statements are retained from
  the fixed r14 report, not reread here. No proof audit is claimed.
- homological.tex, blob 86b7bfafaf7bfc1cddca4b06248118540d545ff8:
  full 466 lines read across consecutive reads, with the small 217-245 boundary
  reread after a combined-output truncation. Includes h:comparison,
  h:duality, h:derived-models, h:stable-image, h:perfect-factor and h:evaluation,
  with proofs. These are the actual complete-Hom, composition and finite
  side-projective evaluation interfaces used. The modified two-base column
  calculation is independently proved, not asserted to be its same-base result.
- bimodule.tex, blob 22d686a1c53d3e765f55e90596bd1c558c3f1686:
  full 696 lines read, beyond r14's lines 1-37. Includes b:bar-model,
  b:profile with its full filtered attaching-map calculation,
  b:ordinary-factorization, b:trace-obstruction, b:stable-adjunction and
  b:evaluated-lift. The source genuinely constructs Y and ordinary g_H for
  nonzero H. Its proof is read for requirements, not audited. It supplies no
  corresponding lift for an arbitrary noninvertible replacement. None is
  asserted here. Our restriction-cone map is ordinary and needs no such lift.
- stable.tex, blob d64c3b8dc60713211bb32deb3d34fa73d87b2a77:
  full 319 lines read (1-100 and 100-319 separately). Includes e:polynomial,
  e:all-degrees, e:socle and e:twists with proofs. The positive/negative weights
  apply to the actual invertible twists. They are not imported into the new
  finite-field restriction calculation. Its negative action is separately proved.
- triangular.tex, blob 04bef4ebcee21dfd9aae285f56e1a43704eeef19:
  full 320 lines read. Includes t:fiber-hom, t:projected-delta,
  t:finite-module, t:end-cohomology, t:vanishing and the negative endpoints.
  The new cone changes the two diagonal base algebras and supplies its own
  block Hom identities, total acyclicity, finite module and comparison formula.
- transfer.tex, blob 0ffb43fdacb838920d5e407effd34301e6291ab9:
  full 132 lines read, including tr:trivial-symmetric and tr:transfer with
  proofs. Positive and a<=-2 negative vanishings are necessary to its vanishing
  conclusion. Before vanishing is imposed its proof gives the decomposition
  used for the new failed construction; the modified-input argument is spelled
  out, including tensor exactness on the complete resolution and nonprojectivity.
- algebra.tex, blob 3a7b197ff4f2ead4e6f676d64131dcc4da6e1c89:
  authenticated and referred to through fixed r14, not reread in this round.
  No new deduction uses its table. Its prior finite-order-resolution failure
  remains a historical supporting result, not a rerun or an all-degree no-go.

The companion AR theorem and conversion interfaces were read in r14 as precisely
recorded there; no new field descent or implication is attributed to them here.
They were not freshly reread, and no companion proof audit is claimed.

## Additional primary bodies inspected for the replacement operation

New retained original PDF/HTML bytes, URL and SHA256 are in
inputs/new-primary-records.json. Local `pdftotext -layout` produced the reading
texts, which the owned input manifest also hashes. No mathematical code in
any source was executed. A later mutable URL is not a verification dependency.

1. Erdmann--Holloway--Snashall--Solberg--Taillefer,
   [Support varieties for selfinjective algebras](https://oyvinso.folk.ntnu.no/Papers/selfinjvar.pdf),
   author-hosted 21-page preprint, PDF SHA256
   0a427a9b6978ab0b0d53fe25a84cebf86599ee7677f00017350f0f4bd029dabe.
   Private ehsst.txt lines 1-345 read, including Introduction, Section 1 through
   Corollary 1.3/Proposition 1.4/Theorem 1.5 and Section 2 through Lemma 2.5.
   Lines 346-420 (Proposition 3.1 and its proof) were additionally read in the
   initial combined extraction; later Section 3/Sections 4-6 are not claimed read.
   Definition 2.1's pushout and Proposition 2.2/Theorem 2.3 are the actual
   side-projective operator-killing construction. Section 2 expressly drops
   finite-generation assumptions; Section 1 and Section 3 keep stated ones.
   Ambient varieties use an algebraically closed field. Our splitting/triangle
   and finite-resolution arguments are algebraic and proved directly over F_2;
   their validity is not inferred by ignoring that ambient hypothesis.

2. Bergh--Sandoy--Solberg,
   [On support varieties and tensor products for finite dimensional algebras](https://arxiv.org/abs/1905.09377),
   downloaded from https://arxiv.org/pdf/1905.09377; retained PDF identifies
   itself as v1, 22 May 2019, SHA256
   e5a29336d3b991f9e8491903efdcf605cd7604318b9a5c58b843c9b6766ef5a5.
   Private text lines 1-289 read through Theorem 2.2 and its COMPLETE proof;
   lines 290-390 read through the discussion of bimodule support and operator
   pushouts. The final discussion/references after 390 were not read. The
   concrete proof uses xi->mu_i xi automorphisms and identifies twisted cyclic
   modules and their support lines. It does not construct a noninvertible
   self-Hom action. Its failure of a general tensor-support formula prevents
   using such a formula for arbitrary replacement bimodules. No such formula
   enters our proof.

3. Markus Linckelmann,
   [Tate duality and transfer in Hochschild cohomology](https://openaccess.city.ac.uk/id/eprint/1949/),
   retained https://openaccess.city.ac.uk/id/eprint/1949/1/1211.5999v1.pdf,
   PDF SHA256 4b77a3a3cee9d995decc28333d979c27c73ccf1c370858e435aa04a648619406.
   Private text lines 67-151 read (Theorems 1.1,1.2 and Remark 1.3);
   lines 172-359 read (Section 2's stable duality, its construction and
   composition identities (2.3),(2.7),(2.8)); lines 365-425 read (remaining
   duality symmetry/Section 3 through the beginning of the adjunction formulas).
   Theorem 1.2's full proof in Section 7 and Sections 4-6 were NOT read or used
   as unproved modifications. Our negative restriction uses explicit
   factorization and invertibility of t, so does not require deriving a new
   negative formula from that theorem's abstract alone. The socle lemma uses
   only the read composition pairing, also stipulated in h:duality.

4. Bohmler--Marczinzik,
   [Tor and Ext vanishing results for commutative Artinian rings, v1](https://arxiv.org/html/2608.09701v1),
   private retained HTML SHA256
   5c9010ae2d125b3477ce70f4947087e5d967ebf34d84ce7d1e4b77acd7496f92.
   Web-rendered lines 197-348 and 415-518 read. The first interval describes
   the exact-zero-divisor two-periodic resolution and Tor between DIFFERENT
   modules. The second contains Theorem 3.1, the finite-field presentation,
   finite Hom-dimension computation and the explicit Ext^3!=0 remark.
   The long list of coefficient supports was displayed but not independently
   checked entry by entry. Embedded code was not executed, and the claimed
   computations were not independently verified. This is a primary screen,
   not a theorem used in any new proof. Neither all-degree Tor for different
   modules nor two self-Ext vanishings supplies the required full self-orthogonality.

## Historical antecedents retained without overreading

Schulz Example 7, Erdmann Theorem 1.1's stated restricted classification,
and Enomoto--Marczinzik's FIXED-coefficient-ring reduction retain exactly the
r14 reading extents in its source-contracts.md. They were not upgraded to
all finite symmetric algebras or to field descent. Their rights and bytes
remain in the authenticated fixed history; no duplicate copies were made.
No worldwide novelty or exhaustive literature search is asserted.
