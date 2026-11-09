# I345 — reading, validation and failure ledger

2026-10-13. The pinned corpus is stipulated true; I344 and prior internal deductions are not. This ledger records the actual reading scope and the repairs used, without representing catalogue summaries or uninspected full papers as theorem evidence.

## Frozen local inputs

Read completely: project AGENTS.md; sources/upstream.json; the I345 brief; the frozen I344 route; and its parent reading note. The route SHA256 matches the prescribed `ba36168c8fea4e7a6cc3ea216e49198eee6853143479f89446df74cb9158fe51`.

Read the complete finalized I236 analytic proof and I239 analytic check, the complete I241 analytic attempt and literature note, and the I230 literature note. I236's analytic SHA256 is `a30077ca36f40e6613e340d3f8ae0ac692000f7b39d6eb4113897f40b7c68931`. Internal lemmas used here were independently expanded in analysis Sections 2, 7–9. I239's PASS is corroborating history, not a replacement for that validation. I230's restricted analytic theorem is not used as an input, so its analytic proof was not needed or represented as freshly read.

The relevant family-377 entry of sources/CONTENTS.md and all paths under the pinned infinity-manuscript prefix in sources/preprints-tree.json were inspected. The catalogue is not a theorem premise. One matching manuscript is listed; no claim of a semantic review of all unrelated manuscript families is made. The initial combined catalogue read was excessively broad and its tool output truncated; only the relevant entry/path inspection is credited.

## Actual pinned manuscript reading

All requests used immutable raw GitHub URLs at the pinned commit. Bodies were held in memory and printed for reading; no new full external body was saved.

- `01-introduction.tex`: complete, lines 1–240; actual thm:main, dimension restriction, normalization and Liouville strategy read.
- `02-flatness.tex`: complete, lines 1–212; infinity lift, critical tests, affine blow-ups, theorem of sums and the entire three-point proof read. The three-point proof is not applied to the modified p-lift equation.
- `03-reduction.tex`: complete, lines 1–377; actual thm:liouville and FIT, all selection, comparison, compactness, failed-fit obstruction and derivative extraction read.
- `04-limiting-tools.tex`: lines 1–224 were read, including complete frame/fit-compactness proofs used for the new finite-tau input. Lines 225–478 were also returned and inspected for the source envelope interface; their homogeneous PDE conclusions are not transplanted to G_tau. No need to assume an altered equation has the source's envelope slope monotonicity.
- `05-envelope-contact.tex`: lines 1–490 were read, including barycentric duality/attainment, spatial semiconcavity, common-time theorem-of-sums calculation and extremal measure construction. The final homogeneous Hamiltonian-slope argument after this range is not used. The altered trace calculation is independently given in analysis Section 9.

Hashes and byte lengths are in input-authentication.json. Reading a stipulated source proof does not reopen upstream truth auditing.

## External primary interfaces

Kotschwar–Ni, arXiv:0711.2291v1 HTML: introduction equations (1.1)–(1.5), actual Theorem 1.1 with every displayed constant, and Section 2 through its final estimate (2.6) and deduction of Theorem 1.1 were read. The proof estimates only the noncritical set where f>0; ordinary weak p-harmonic regularity supplies C1 and smoothness there. Division is by p-1, not by an original gradient. No claim of reading the remaining flow/entropy sections is made.

Savin: read complete existing extractions of PDF pages 1–4 and 14–18, and checked the primary PDF interface through the author's URL. H1/H2/H4, Theorem 1.3, and all of Section 4/Proposition 4.1 were used. The existing text loses some glyphs; the argument here needs structural dependencies rather than numerical threshold values. The varying-operator proof and common local C2 bounds justify parameter uniformity. The amplitude family separately pays proportional derivatives. No full-paper proof read is claimed.

Julin–Juutinen: read the complete existing arXiv:1104.2197v1 pages 1–6 extraction. Definitions 2.1–2.3, the p>=2 equivalence theorem and Remark 3.3 are the used interfaces. Tests at zero gradient in the polynomial homogeneous operator have value zero; no division there is used. Its p-Laplace theorem is not substituted for the finite-tau exponential flux, whose convolution/Fatou passage is reproved.

Uhlenbeck: primary PDF fetched into memory from the Tsinghua archive, SHA256 `bb041a82ffd0b1c7e1b694a162aac642c2755dfd3bf00726e443ac8106e7239a`. Pages 1–4 and 9–22 were extracted and read. This includes the exact main/scalar statements, (3.2), all of Sections 4–6, quantitative (5.4), its decay choices, and Bernstein theorem (6.1). PDF pages 5–8 were not freshly read and are not claimed so. For compact-p coverage, the proof choices in Sections 4–5 are checked with s=(p-2)/2 in a compact interval, a common K and a fixed positive continuity exponent. The familiar assertion “constants depend on p” alone was not treated as proof of compact-p uniformity.

Crescimbeni–Forzani–Perini: read the complete existing PDF pages 1–5 extraction. Exact symmetric measurable-coefficient hypotheses (2.1), weak-solution definition (2.2), and solution Harnack/Hölder interfaces (2.5), Theorems 3.1–3.2 read. They apply to the linear Dirichlet replacement w, not indiscriminately to a nonlinear viscosity difference or an arbitrary weak supersolution. The two-dimensional case can be lifted to three dimensions if using this exposition's n>2 Sobolev formula.

## Failed shortcuts and repairs

**Unmodified p-harmonic lift:** false as a claimed invariance. For smooth u, the actual p-Laplacian of u+b adds a transverse trace coefficient different from the original one. Section 3 proves the correct modified equation by Schur complements, including g=0. No tilted-hyperplane shortcut for the Laplacian is used.

**Uniformity from value convergence alone:** insufficient for derivatives. The repair is expanding domains plus entire Lipschitz rigidity. Compact-p and infinity limits are identified via continuous polynomial viscosity operators, then rigidity/scaling. This proves qualitative affine flatness before any power-rate conclusion.

**On-constraint operator treated as global:** unjustified. The repair is max(C_i,0) for finite-viscosity compactness and max(B,0) for the Savin family. These extensions are globally elliptic and coincide at every actual upper/lower test, with local smoothness where Savin needs it.

**Negative base A or viscosity ignored:** unjustified near original critical slopes. One bounded quadratic contact supplies A_i>=-C lambda_i; as epsilon_i->0 this forces liminf nu_i>=0. The argument needs only a contact somewhere, not a pointwise test-gradient theorem.

**Finite anisotropic trace passed to I236 directly:** invalid without its PDE/fit contract. Exact transport makes V linear along a and removes that Hessian direction. The projected shear increments give FIT for W with the original C0. This is a new checked reduction.

**I344's cross-parameter norm transfer:** the quoted source lemma applies to equal parameters. The initial Lambda lambda versus eta=kappa lambda fit needs an extra argument. A common-axis segment of length O(r/sqrt(kappa)) yields O(kappa^2 lambda) in norm; the equal-eta chain then adds O(eta log nu). Its relative error tends to zero against A=nu lambda/epsilon. The stronger I344 display was not assumed.

**Savin absolute C2 bound used as proportional:** insufficient. The amplitude d family, including d=0, has common local ellipticity/smoothness. Rescaling the solution yields ||D2W||<=C||W||, paying the physical C e/H estimate.

**Large-nu limiting PDE alone:** insufficient. Nonaffine time functions solve the divided horizontal trace equation. They are not counterexamples to actual-p regularity. The repair uses the finite-p equation on an available H=nu^2 r cylinder and a small-amplitude ellipsoid; no such limiting-PDE example is reported as refuting the target.

## Access failures and scope discipline

The first PDF extraction attempt used unavailable Python module `fitz` and did not fetch or save a body. The Tolksdorf CORE URL returned HTTP 403 through both web and the in-memory HTTP attempt. That theorem's text is not credited as read and it is not a premise. The independently accessible primary Uhlenbeck theorem/proof replaces it. `pdftotext` via stdin/stdout parsed the Uhlenbeck PDF in memory.

Several combined read outputs were truncated. Needed omitted local/source ranges were subsequently read in bounded calls; the scopes above distinguish complete and partial readings. No numerical scans or source-body files were produced. All persistent writes were restricted to the five assigned paths. No subagents, git, live-sibling reads, publication, staging, commits, shared indexes or earlier-evidence edits occurred.

## Final research disposition

The repaired argument proves the unrestricted target relative to the stipulated corpus and the stated classical interfaces. Independent review must check the complete new proof and contribution rather than regard this research verdict as acceptance. Literature priority and explicit constants/exponents remain unclaimed; no mathematical hypothesis gap is intentionally retained in the candidate theorem.
