# I216 — primary literature and source-dependence ledger

Exact local identities, pinned URLs and reading limits are in `../../experiments/i216_relative_sobolev_collar/input-authentication.json`. Existing source copies were read in place. **No new source copy was retained:** the new local files are the four assigned notes plus their authentication JSON. Web-only inspections below are identified as such; they do not carry invented file hashes or full-read claims.

## The decisive prior overlap is in the pinned source itself

High-range family 368: [pinned smooth cubical cutoff and related operations](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Strong-diffeomorphic-approximation-in-three-dimensions-for-p-gt-2-September-24-2026/build/sections/05-high-preparation.tex).

- `hp:cutoff` permits tame collapsed fibers and by itself does not provide energy-controlled opening.
- **`hp:smooth-cutoff`** instead takes a smooth diffeomorphism and returns a locally bi-Lipschitz, image-preserving exact inner identity with transition energy bounded by the input's nearby energy plus arbitrary ε₀. Lines 1945–2046, statement and proof, were read. This is the operation omitted from the supplied I213 reduction.
- Its proof fixes finitely many normalized smooth fillings, then suppresses their forward derivative contribution by strictly positive target squeezes. The constants may depend on the individual input; the energy inequality's C_p does not.
- `hp:full-rank-correction`, lines 2078–2250 read, already applies this exact operation to smooth ordinary approximants and absorbs shell energy. Therefore the mechanism is paid even before I216's inversion of which side is corrected.
- `hp:carrier`, statement and initial proof through line 1710 read, and `hp:opening`, full statement/proof read, were checked separately. Neither is misquoted as a prescribed-collar Sobolev theorem.

The [pinned smoothing section](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Strong-diffeomorphic-approximation-in-three-dimensions-for-p-gt-2-September-24-2026/build/sections/02-smoothing.tex) was read **in full**, lines 1–1019. Its finite PL libraries, good/bad cube estimates, local edge and vertex smoothing, and variable convolution justify the support-preserving specialization proved in analytic §3. A generic qualitative relative PL theorem is not substituted for these derivative estimates.

Both range companions' main theorem statements were checked. The high-range introduction was read in full; the low-range introduction was read through line 85. They assert smoothness on open domains and do not state exact smooth boundary data. The high-range final assembly, lines 1130–1258, was read; it invokes `hp:full-rank-correction` and smooths afterwards. The boundary theorem proved here is therefore an implicit source consequence via localizing paid operations, not a verbatim main-theorem clause and not a new substantial bridge.

## Primary comparison: exact relative approximation is established prior art in the plane

T. Iwaniec, L. V. Kovalev, J. Onninen, *Diffeomorphic approximation of Sobolev homeomorphisms*, [arXiv:1009.0286v1](https://arxiv.org/abs/1009.0286v1), [DOI](https://doi.org/10.1007/s00205-011-0404-4). Existing local PDF/text: `../i213_new_analytic_geometric/iko-1009.0286v1.{pdf,txt}`. I216 read text lines 1–130, including Theorem 1.1 and its five conclusions. This is a narrower read than I213's full-paper read. The theorem already has zero-trace errors and compactly supported modification for a map smooth outside a compact set. It is planar and is not imported as a three-dimensional estimate.

S. Hencl, *Ball–Evans approximation problem: recent progress and open problems*, [arXiv:2502.01336v1](https://arxiv.org/abs/2502.01336v1). Existing local `../i07_analysis/literature/hencl2025.txt`: only lines 1–220 reread here, for context, not a fresh full-paper assessment. I213's supplied literature record describes its broader reading. I216 does not infer current open status or priority for LD_p from that report.

## Primary comparison: piecewise affine smoothing

D. Campbell, L. D'Onofrio, T. Vítek, *Diffeomorphic approximation of piecewise affine homeomorphisms*, [arXiv:2507.02854v2](https://arxiv.org/html/2507.02854v2), [published article](https://doi.org/10.1007/s12220-026-02398-w).

Web-only reading: versioned HTML introduction through Theorems A/B and the beginning of preliminaries (rendered lines 27–94), plus publisher metadata/abstract and Theorem A. It treats locally finite piecewise affine inputs in dimensions three/four, with forward and inverse derivative error. The publisher identifies publication on March 31, 2026. No full-proof read or local copy is claimed. No arbitrary-rough-input collar correction or uniform linear defect estimate is inferred. The operative smoothing proof for I216 is the fully read, stipulated pinned source.

## Primary comparison: ambient deformation versus derivative control

R. D. Edwards, R. C. Kirby, *Deformations of spaces of imbeddings*, Ann. Math. 93 (1971), 63–88, [primary PDF](https://www.maths.gla.ac.uk/~mpowell/Edwards%20Kirby.pdf), [DOI](https://doi.org/10.2307/1970753). Web-only reading: introduction and definitions, rendered PDF lines 14–140; Theorem 5.1 statement and its introductory context (rendered lines 299–343), plus returned nearby excerpts, not its complete proof. The compact-open topology and supported extension statements justify the qualitative comparison only. No L^p velocity or derivative estimate follows from the statements inspected. The actual local ambient extension used in the source is read in `sm:local-extension` with its stated controls.

J. Li, J. A. Watts, *The orientation-preserving diffeomorphism group of S² deforms to SO(3) smoothly*, [arXiv:0912.2877](https://arxiv.org/abs/0912.2877). Bibliographic/title-page check only; no full proof imported. The pinned `hp:smooth-cutoff` proof already uses smooth sphere isotopy for each fixed filling. No uniform quantitative bound is inferred from this title or from the smooth-dependence assertion cited in the pinned proof.

The Hatcher 3-manifold notes URL cited by the source was opened once via the web tool and returned `Internal Error`. No external read is claimed for it. Smooth ball filling is used as the already accepted operation explicitly in the pinned smooth-cutoff proof, not as a new inference from an unread PDF.

## Search scope and contribution limit

Two bounded web search batches looked for three-dimensional prescribed-boundary approximation, quantitative Sobolev annular extension, and the primary piecewise-affine paper. Irrelevant search hits and secondary summaries were not imported. The queries and inspected URLs are in the authentication JSON. No exhaustive search or worldwide novelty claim is made for LD_p.

Conclusion: I216 proves the exact-boundary target using the **already paid smooth-input cubical cutoff**, a fixed inverted collar, and support-preserving use of the source smoothing proof. Its quantitative estimate is weaker than a linear error retraction. The proposed stronger LD_p in analytic §6 remains unpaid and is not nominated. The distinct isotopy route in §5 records an exact sufficient velocity estimate, not a theorem of Edwards–Kirby or Smale.
