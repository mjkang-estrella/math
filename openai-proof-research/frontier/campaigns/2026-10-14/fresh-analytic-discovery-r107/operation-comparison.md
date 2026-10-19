# Paid operations, additional deduction, and contribution uncertainty

This is an author comparison, not an independent contribution gate. It supplies
the actual reduction for a parent reviewer to judge. It requests no acceptance
credit. The frozen theorem is proved at author level in `proof.md`.

| Operation | Already supplied | What this note adds |
|---|---|---|
| Arbitrary smooth closed surface immersed isometrically in R4 | Source333 `thm:main` | No new immersion existence theorem |
| Finite spherical preparation, strict shortness, metric decomposition, convex phases, boundary crossing preparation | Source333 `lem:spherical-preparation`, `lem:global-preparation`, complete proof | Choose the starting ordinary spherical immersion to be an embedding; retain it under the already available C1-small preparations |
| Smooth velocity loop of any required amplitude, including turning and large arcs | Source333 `lem:velocity-loop` | No change to its construction, phase, parameter, sign, or amplitude |
| Finite periodic expansion, mean correction and all-order exact correction | Source333 `lem:finite-periodic-expansion`, `prop:small-increment`, `prop:exact-correction`, `prop:primitive-realization` | No new PDE estimates or correction scheme |
| Uniform derivative asymptotics for the exact maps; exterior C2 closeness | Source333 `eq:realization-asymptotics` | Derive global C0 closeness directly from the mean-zero first derivative and one exterior anchor |
| P=span(F_y,F_yy)^perp and its relation to the normal plane | Source333 `lem:velocity-plane` already uses the transverse geometry | Explicitly use the complementary-plane property to construct a global oblique tubular projection |
| Propagation of preferred normal, nonzero second form and all later boundaries | Source333 `geometry-preservation.tex` | Impose one additional small-scale threshold, for injectivity |
| Embedding preservation for general oscillatory deformations | Classical tubular projections and C1 openness; corrugation-specific preservation is explicit in primary literature below | Show that the source's entire order-one derivative oscillation is annihilated by the oblique projection, so its composite with the exact map is C1-close to the old embedding |
| Finite assembly at the prescribed metric | Source333 final proof | Apply the injectivity observation at every existing finite step |

The strongest reason this might qualify as a distinct deduction is that global
injectivity is absent from the source theorem, and C0 closeness alone cannot
preserve it. The proof uses a specific complementary bundle and a projection
estimate to bridge this gap, with no smallness restriction on the added metric.
It is not obtained by merely replacing a parameter, sign, degree, or dimension
in a paid formula.

The strongest reason it might fail the substantiality gate is that the source
has already paid for the full analytic construction and for the relevant
transversality. Once those contracts are read, the new argument is a short
application of classical tubular geometry to a finite sequence. It may therefore
be a source-companion corollary or a technical embedding-preservation adaptation.
A striking headline in isolation is not a reason to override that objection.
No author label resolves this issue; the parent must assess it separately.

## Actual closest primary operations

**De Lellis–Inauen–Szekelyhidi, 2018.** Theorem 1.2 includes preservation of an
initial embedding for C^(1,1/5-delta) isometric maps of a disk into R3. Remark 8.1
provides the finite-step preservation argument, by separating close and distant
domain pairs. The final proof of Theorem 1.2 again controls both types of pairs.
The paper explicitly treats embedding preservation as classical Nash–Kuiper
machinery. Its theorem is neither a smooth nor a closed-surface R4 theorem.
We do not import a mean-value representation for a vector oscillation from that
argument: the direct projection proof in `proof.md` supplies the needed estimate.
This comparison is evidence of a serious standard-method objection, not a proof
of an independently adjudicated TECHNICAL verdict.
[Published primary paper, pp.1121,1140–1141,1143–1144](https://ems.press/content/serial-article-files/38715).

**Cao–Szekelyhidi, arXiv:2306.12879v1.** Theorem 1.1 gives C^(1,theta)
isometric embeddings of compact manifolds in dimension 2n in its stated Holder
range. Its Proposition 3.3 and complete single-step proof use normal oscillation
and smaller tangential terms. The last paragraph on p.14 refers to the preceding
paper for standard preservation of embeddings. This is close methodological
antecedence, but not the smooth R4 theorem. Our step uses a possibly non-normal
complement and the source's already exact smooth corrections.
[Version-locked primary PDF](https://arxiv.org/pdf/2306.12879v1).

**Le Donne, arXiv:1005.1623v2.** Section 3 constructs path-isometric embeddings
by a sequence of approximating embeddings and control of tubular-neighborhood
intrinsic distances. Lemma 3.5 states that tube-distance fact and credits an
earlier reference; it does not present its full proof. The construction and
injectivity conclusion were read. This is another established use of tubes and
separation in metric embedding constructions. Its limiting path-isometry
argument does not assert the present smooth exact R4 conclusion.
[Version-locked primary PDF](https://arxiv.org/pdf/1005.1623v2).

**Gromov, October 9, 2015 author manuscript.** The inspected passages discuss
elliptic surface immersions in R4 and Nash twists, and later smooth closed
immersions in R5. These are contextual comparisons only; the incomplete read
does not establish a priority clearance for the present target.
[Author PDF](https://www.ihes.fr/~gromov/wp-content/uploads/2018/08/nash-copy-Oct9.pdf).

The original Nash, Kuiper, Federer, Poznyak and Gromov PDR proof bodies were not
read here. Their references in the inspected papers are not upgraded into
full-body reading claims. No claim of worldwide novelty follows from this search.

## Prior developed family333 chains

The complete `fresh-parent-discovery-r5/screen.md` derives finite exterior C^m
control by changing already-paid finite accuracy parameters. It explicitly leaves
noncompact exhaustion compatibility open and warns against arbitrary prescribed
compact-map extension. Our proof requires neither refinement nor extension: it
uses closed M, the original C2 exterior contract, and finitely many steps.

The complete `fresh-analytic-discovery-r17/source-reading.md` records an earlier
source333 navigation screen without an embedding proof. The complete
`fresh-structural-discovery-r92/screening.md` rejects a prescribed-regular-homotopy
extension using the positive-curvature obstruction to nonzero normal Euler class.
Our original frozen theorem prescribes no regular-homotopy or knot class and
uses an initial embedding with a global normal. Neither old failed target is
silently weakened and recounted here. Distinctness from those attempts still
does not establish substantiality.
