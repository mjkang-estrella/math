# I231 — reading scope, failed routes, and limitations

## Process and early record

The initial analytic note was written after reading the exact source fit contract and source 04/05 operations, before the main literature investigation or a conclusion. It recorded the new trace correction, the divergence identity, the absence of uniform ellipticity, and the infinite-tau counterexample. A later intermediate entry recorded the surviving barycentric operation and the external strong-comparison warning. Those entries remain in analytic-attempt.md; the final verdict explicitly supersedes their provisional status.

Work stayed in /home/mj-kang/Documents/Dev/math/openai-proof-research. Only the assigned I231 iteration, two experiment notes, authentication JSON, literature file, and actually read page excerpts were written. No subordinate agent, live other-agent output, I230 file, numerical experiment, parameter scan, research script, test, snapshot, seal, giant historical replay, shared ledger edit, staging, commit or publication was used. Shell/Python use was limited to ordinary source-local lookup, text extraction, retrieval and provenance. Some initial filename-only searches returned unrelated paths and were narrowed; no unrelated file contents were used.

The supplied I224/I228/I229 completed documents were context, not new proof inputs. The completed I228 authentication file was read only to locate the existing pinned manuscript copy. The existing I224 literature file was read to locate prior source copies. No historical iteration corpus was replayed and no claimed open estimate in those supplied documents was silently inherited.

## Actual pinned source reads

Reused corpus prefix:

    frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/
      Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/

* AGENTS.md and sources/upstream.json: complete.
* sources/CONTENTS.md: family 377, lines 9125–9142 only; matching lines were also displayed by source-local lookup.
* sources/preprints-tree.json: only matching entries for the exact family-377 prefix, for manuscript/companion inventory and blob verification; full catalogue semantics were not read. One manuscript and its build/figure/bibliography assets occur in that family.
* README.md: complete. 01-introduction.tex: lines 1–90, including thm:main and cor:interior-c1. Its exact homogeneous conclusion is not applied to the new equation.
* 02-flatness.tex: lines 80–135, including full definitions and statement of lem:sum-rule. Its PDE-free matrix operation is used; prop:three-point is not applied to viscous solutions.
* 03-reduction.tex: lines 1–145. The full thm:liouville and exact all-center/all-radius sheared fit contract were read. The family flatness and beginning of scale selection were contextual. No homogeneous theorem is relabeled viscous.
* 04-limiting-tools.tex: complete, 478 lines. Frame invariance was recalculated for the trace term; geometric fit estimates/compactness were checked. Quadratic envelope convexity and slope monotonicity require changed PDE inputs and are not reused unchanged.
* 05-envelope-contact.tex: complete, 597 lines. Finite barycentric attainment, duality, compactness of normalized configurations and tail integrability use no PDE. Common-time/subsolution steps were redone with the trace. The preliminary horizontal-affine case was replaced by a fit-only proof. Finite Hamiltonian/contact-slope claims remain unavailable.
* 06-discrete-propagation.tex: lines 1–270 only. The exact drift identity and its proof were read and the trace loss calculated. Later velocity bounds and frame lemmas were not read or invoked as theorem inputs.
* 07-contact-localization.tex: lines 1–115 only, including prop:contact-propagation and the first stopped-expectation argument. Its required finite slope, drift and uniform expectation bounds fail to be supplied here. The rest of its proof was not read or invoked.
* 08-rigidity.tex: complete, 119 lines. Its constant-envelope-slope hypothesis is not obtained for G_tau and the lemma is not applied.
* bibliography.tex: lines 1–45 were incidentally displayed during source-local checking, not used as primary evidence for external theorem statements.

Pinned files are reused in place. Their hashes and matching Git blob IDs are recorded independently. Truth of every pinned operation remains stipulated; this note checks only its new inputs.

## Primary literature actually read

1. Sánchez Morgado, arXiv:1712.10275v1: PDF pages 1–5, retained and fully read. The Euler–Lagrange equation (4) includes exactly G_(1/k) for the free quadratic Hamiltonian. The eigenvalue discussion explicitly notes growth/decay with the gradient. Lemma 1 and Theorem 1 concern classical periodic solutions. They are not a theorem about all continuous entire solutions with logarithmic fit control. The step with sigma inverse in the displayed gradient proof does not provide a verified parameter-independent estimate here; no audit or correction is claimed.
2. Porretta, arXiv:2203.04856v1: PDF pages 1–7 and 8–13, both retained and fully read. Equation (1.7) matches after u=-V. Read Theorems 1.1–1.3, assumptions (2.3)–(2.11), Lemma 3.1 and Theorem 3.4 with its proof, plus the remaining statements through Theorem 3.7. The gradient bound is for smooth solutions of a prescribed boundary problem and depends on epsilon, boundary density norms, potential and solution bounds. These inputs are absent in the target class. Pages 14 onward, including the appendix, were not read.
3. Ohnuma, 2006 RIMS note, PDF pages 1–5 through web text; pages 2–5 separately retained and fully read. The local ellipticity and gradient-local Lipschitz hypotheses F1–F3 and Theorem 3.1 look applicable formally. Its remaining proof was not relied on and was not retained. A nonretained pipe extraction displayed initial portions again; this did not create an additional source copy.
4. Ohnuma–Sakaguchi, arXiv:1806.03587v1: PDF pages 1–4, retained in two excerpts and fully read. The introduction explicitly reports that the earlier Giga–Ohnuma argument fails for gradient-dependent nonuniform ellipticity. Theorem 2.1 instead addresses prescribed mean curvature. Web HTML lines about its classical-replacement argument through the start of its contradiction were also read (approximately lines 30–214); the entire later proof was not read or applied. The broad older theorem is therefore not a paid dependency.

Bounded web searches included combinations of viscous Aronsson/Liouville, gradient-dependent strong comparison, periodic weak KAM exponential functionals, and entropy planning. Search snippets were leads only. Irrelevant parabolic infinity-Laplacian, Bellman, conformal and p-Laplacian results were not adopted. One Hokkaido PDF request returned an internal error; no copy was retained. No search miss establishes novelty. Other external papers cited within these excerpts were not automatically treated as read.

## Route failures that matter

* Positive definiteness of A_tau at finite p does not produce a global ellipticity constant: one eigenvalue tends to zero as |p| grows. The fits allow both t log|t| and the smooth spatial example x1 sqrt(log(e+x1²)); the latter is proved to have C0=10 on every sheared box. Thus no global horizontal gradient estimate follows just from fit geometry.
* Ordinary quadratic-envelope convexity is replaced by an l log l correction with singular zero-length derivative. Finite Hamiltonian slopes and the original random-walk submartingale are not established.
* The trace does cancel for common spatial translations in the barycentric envelope. This pays construction of an extremal subsolution contact, but propagation of that contact remains SC_tau, explicitly unpaid.
* The exponential divergence identity is a classical identity. A continuous viscosity solution has not been shown to have the needed gradient/energy integrability. No variational estimate is applied across that gap.
* A hypothetical uniform local C^(1,alpha) estimate REG_tau for the centered class would pay the entire independent growth route; the large-scale logarithmic factors and drift were explicitly retained. REG_tau has not been proved by calling the equation elliptic.
* The infinite-tau PDE-plus-fit package is false via sin t. This does not manufacture an exact finite-tau counterexample or establish attainability of sin t as a limit of entire fitted solutions.

## Final scope

Finite positive tau: unresolved by this investigation, with two exact sufficient missing statements. Infinite tau after retaining only the divided PDE and fits: disproved. No quantitative uniform p-harmonic gradient bound, full p-to-infinity convergence result, worldwide novelty certification, acceptance-count change, or positive contribution verdict is asserted. Parent gates remain independent.
