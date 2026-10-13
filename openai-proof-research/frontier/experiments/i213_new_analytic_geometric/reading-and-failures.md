# I213 — reading and failure record

Pinned premise: OpenAI/math `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. All its theorems/lower operations are stipulated. This is discovery, not an upstream audit.

## Work sequence and scope

1. Read `AGENTS.md` and `sources/upstream.json` in full. Read catalogue entries 354/368/377. Parsed `sources/preprints-tree.json` only for relevant manuscript paths and blob identities; the truncated root-tree cache was not used.
2. Searched the four status ledgers and iteration Markdown with Ball–Evans, infinity-harmonic, cubic/three-torus, isoperimetric-profile and family-number terms, excluding filenames beginning `i211` and `i212`. Initial broad numeric matching in the tree was noisy and yielded no semantic conclusion; it was replaced by exact manuscript-path filtering. The positive matches, not search misses, drove the decision. Read the relevant I43, I07, I130, I140 and I143 passages. Did not replay their recursive audits or verify historical artifacts.
3. Wrote partial I213 notes immediately after target selection. Selected exact smooth boundary-trace approximation, distinguished from I07's inverse-energy/incompressible target. No fourth family was screened.
4. Read both pinned approximation introductions fully. Read high-range smoothing lines 1–210, including `sm:smoothing`, `sm:relative-pl`, `sm:local-extension`, `sm:proper-degree` and their displayed proofs; read corresponding low-range lines 1–80. Searched labels throughout the high smoothing/assembly files for additional relative promises. Read high preparation `hp:opening` with proof and `hp:carrier` statement/initial construction; read the entire final high-range main-theorem proof (lines 1140–end). These are operation-level scopes, **not** a claim to have read every page of the long manuscripts.
5. Read the torus `paper.tex`, `preliminaries.tex` and `elementary-estimates.tex` fully. The first is a main file with inputs, not the concatenated whole paper. Read the infinity-harmonic introduction fully. Those rejected screens rely on actual statements and positive ledger overlap, not a fresh proof audit of their full machinery.
6. Read Hencl's existing `hencl2025.txt` throughout, with overlapping rereads of lines 1120–1350 and 1340–2290 to recover the initially truncated center. The extraction contains HTML chrome and duplicated formula renderings; these are not mathematical source variants. The versioned URL is in its existing manifest. Read that manifest for provenance, without copying either source.
7. Retrieved only one new primary manuscript: Iwaniec–Kovalev–Onninen `1009.0286v1`, saved the PDF and extracted text. Read all 1044 text lines in three nontruncated chunks (1–360, 361–720, 721–1044), including the proof and references. This is full mathematical-text reading via extraction, not visual page-layout review. The current arXiv page lists only v1. Online arXiv metadata and the publisher identified Campbell–D'Onofrio–Vítek's piecewise-affine smoothing theorem (v2; 2026 publication); no full-proof reading is claimed for that external paper.

All read-input identities and exact paths are in `input-authentication.json`. Existing pinned sources were read in place. No corpus mirror, source snapshot, or seal was created.

## Failures and distinctions that determine the verdict

- Torus fixed-volume stability and homogeneous infinity-harmonic interpolation are already classified as technical. Counting their reformulations would repeat prior work.
- Source smoothness on open domains does not mean smoothness on the closed ball. A positive tolerance tending to zero at the boundary gives equality of continuous boundary traces, not derivatives or exact open-collar agreement.
- `sm:relative-pl` assumes existing PL data and is qualitative. `hp:opening` concerns its constructed carrier and is likewise not a Sobolev error estimate. `hp:carrier`'s exact cores cannot silently be replaced by a prescribed collar in every downstream stage.
- A1 inserts an identity collar with strong convergence, but does not smooth the rough interior. A2 flattens an already smooth boundary-fixing map, but cannot be applied to open-domain approximants with uncontrolled boundary derivatives.
- For the ambient route, strong convergence with p>3 gives uniform values and room between nested spheres. It supplies no derivative estimate for the topological annular extension.
- The fixed-cutoff candidate fails in an explicit smooth triangular example, even with uniformly bounded forward derivatives. Its minimum Jacobian may tend to zero; no common inverse Lipschitz bound is asserted. The counterexample does not exclude a map-dependent or nonlinear correction and cannot be promoted to a nonexistence result.
- The primary planar theorem already has relative conclusions and an energy mechanism. The proof uses a planar injectivity theorem for p-harmonic coordinate replacements. Transplanting its conclusion to dimension three without that mechanism would be circular.

Final status: **B_p, C_p, (CS_p) unproved here; technical A1/A2/B1/B2 proved as written.** No PROVED NOMINATION, no accepted-count proposal. Parent owns independent proof and contribution reviews.
