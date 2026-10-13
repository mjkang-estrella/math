# I219 — independent contribution review of the global Neumann eigenmap

**Disposition: TECHNICAL/KNOWN ONLY.** This means **routine under the accepted source operations**, not that an exact earlier publication of the entire eigenmap statement has been located. The result is an attractive qualitative corollary, but the evidence does not support counting it as a substantial independent bridge beyond the stipulated theorem. This is a contribution assessment only. I218 was not read; no proof-gate decision or count change is made.

## Scope and exact claimed content

Let Ω be a nonempty bounded simply connected planar domain with C∞ boundary. Let μ be its first positive Neumann eigenvalue and V its real eigenspace, with dim V = 2. For any basis u,v, I214 claims that F = (u,v) is an analytic diffeomorphism of Ω onto a bounded, smoothly and strictly star-shaped domain containing zero; that F extends to a homeomorphism of closures with a smooth embedded boundary curve and strictly monotone boundary polar angle; and that all nonzero first-mode nodal arcs pass through one common interior point. These are one package.

The exact restriction to a double *same-eigenvalue* eigenspace is essential. This is not a theorem about the first two positive eigenfunctions when their eigenvalues differ. Nor is it a smooth embedding of the closed two-dimensional domain: the normal derivative of F vanishes at the boundary.

## Actual pinned operations

I read in place all six sections, main.tex, README, references.bib and the boundary-sign figure source retained for I214. Their Git blob hashes were checked against the exact family entries in sources/preprints-tree.json at the stipulated pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. No companion manuscript is listed in that family.

The operative source statements are:

- `01-introduction.tex`, `thm:main`: every nonzero w in V has ∇w ≠ 0 throughout Ω, with no simplicity assumption.
- `02-preliminaries.tex`, `lem:nodal`: both strict sign sets are connected; four alternating strict boundary signs are impossible.
- The same section, `lem:gap`, `lem:boundary-weight`, `lem:conformal`: μ < λ_D; a fixed positive boundary weight makes every trace mean zero; and the smooth conformal disk parametrization is available.
- `prop:multiplicity` is already a lower operation, not new here. Smooth boundary regularity and interior analyticity are also supplied.

Sections 03–06 contain the vector variational equality space, boundary multiplier identity, reciprocal-kernel result and their use to prove the gradient theorem. None states the global eigenmap. However, the proposed eigenmap argument does not discover another use of these analytic operations: it takes their completed output, ∇w ≠ 0 for all w, as its starting point.

## What is already known, including the boundary issue

The closest overlooked comparison is Bérard–Helffer, *Upper bounds on eigenvalue multiplicities for surfaces of genus 0 revisited*, arXiv:2202.06587v1 (2022), §§3.1–3.2 and 6.2–6.4.5. Theorem 3.3 and Corollaries 3.4, 3.8 supply finite-order boundary jets and finite nodal graphs on smooth boundaries, including Neumann. Property 6.3 classifies second-mode nodal sets on a simply connected domain. Section 6.4.2 excludes the circle and boundary-based loop alternatives for the Neumann Laplacian by Dirichlet eigenvalue comparison, explicitly discussing contact at isolated boundary points. Thus the remaining case is precisely one regular arc with two distinct simple boundary zeros. This precedes, and does not require, the stipulated interior-gradient theorem. [Primary text, version v1](https://arxiv.org/pdf/2202.06587v1).

Consequently, I214's reflected-PDE/Carleman/ends-count development is not new boundary spectral structure. It may be a self-contained way of recovering established ingredients, but its length must not be mistaken for independent contribution. The current assessment does not audit that Carleman proof.

Once the two-simple-endpoint fact is available, the boundary eigenmap conclusions are short linear algebra and circle topology. If F(p)=0, a nonzero coefficient vector perpendicular to Fτ(p) produces a first mode whose value and tangential derivative both vanish at p, impossible. Applying the same endpoint fact to the coefficient vector perpendicular to F(p) gives det(F,Fτ) ≠ 0. Exactly two boundary zeros per combination makes the resulting circle covering have absolute degree one. A positive smooth polar radius and strict star-shapedness of this boundary curve then follow. These deductions use old nodal structure and dimension two, not a new boundary analytic theorem.

## What remains beyond the known ingredients

For dim V = 2, the stipulated gradient conclusion is exactly the pointwise assertion det DF ≠ 0: a singular derivative matrix is equivalent to a nonzero combination with zero gradient. This equivalence alone is already paid and is not my reason for calling the *global* result routine.

The additional step is the familiar one-dimensional monotonicity mechanism for planar univalence. On the connected zero arc of w = a·F, an independent coordinate z = b·F has tangential derivative

    dz(T) = det(∇w,∇z) / |∇w|.

It has one nonzero sign. A putative double value y is handled by choosing a perpendicular to y; both preimages then lie on that single arc, where z is strictly monotone. This is a short rotation-dependent variant of the standard connected-level-set criterion, documented in Braun–Llibre, Corollary 7 and the paragraph following it. Their stated criterion assumes all levels of one fixed coordinate are connected; I214 instead uses zero levels of all rotated coordinates. The hypotheses are not identical, so that paper is **not** an exact theorem subsuming I214. The mechanism, however, is the same elementary monotonicity argument. [Primary paper](https://msp.org/pjm/2024/333-1/pjm-v333-n1-p01-s.pdf).

After injectivity, the zero-containing star-shaped image follows from the origin-line interval property and mean zero, or from the boundary winding number and the constant Jacobian sign. The common nodal center is F⁻¹(0), and the intersection statements are pullbacks of intersecting origin lines. These are valuable descriptions of the same coordinates, not further independent spectral phenomena. I regard the origin-separation observation as a small genuine topological deduction, not a substantial new spectral bridge.

There is also a useful precise sense in which this is an equivalent geometric reformulation: within this double first-mode setting and with the established nodal facts available, the stipulated all-combinations gradient property implies the claimed global interior coordinates; conversely an interior diffeomorphism immediately implies that gradient property. The global language adds clarity and geometric consequences, but not another independent analytic restriction on this class of domains.

## Spectral-embedding comparison and concrete significance

I read the complete 45-page Jones–Maggioni–Schul full preprint, arXiv:0709.1975v4, not just the PNAS announcement. Theorems 2.1.1 and 2.2.1 select d eigenfunctions at frequencies comparable to the inverse square of a chosen local radius and prove quantitative local bi-Lipschitz coordinates. The introduction also discusses global coordinates from a larger spectral band on closed manifolds. Thus “previous work is only local” is too sweeping. It supplies neither a fixed double first Neumann eigenspace theorem nor I214's boundary conclusion. [Full primary preprint](https://arxiv.org/pdf/0709.1975v4).

I also read Bates's full 16-page paper: Theorem 2 establishes global embeddings using finitely many initial eigenfunctions, uniformly over a class of closed manifolds with controlled geometry. It is a genuine global comparison but does not identify two first modes on a bounded planar Neumann domain. [Primary author version](https://arxiv.org/pdf/1605.01643v1).

The concrete value of I214 is therefore an exact, dimension-minimal qualitative coordinate representation for the smooth double-first-mode class, plus a basis-independent distinguished point. It is not empty: the disk already lies in the class. It can clarify what two-mode spectral plots represent. It supplies no distortion estimate, conditioning bound, stability result across eigenvalue splitting, or extension to unequal modes. The degeneracy at the boundary is especially material for computational parametrization. This useful interpretation falls short of a substantial independent contribution after the strong source theorem and classical nodal structure have been paid for.

## Other comparisons and mathematical cautions

Alessandrini–Nesi's *Invertible harmonic mappings, beyond Kneser*, Theorems 1.1–1.3 and 2.1–2.2, distinguish harmonic univalence from general monodromy. Their harmonic criteria do not apply directly: F solves (Δ+μ)F=0, not ΔF=0, and its boundary Jacobian is zero. Strict star-shapedness also cannot be substituted for convexity in the Radó–Kneser–Choquet theorem. The general degree/monodromy mechanism remains classical. [Primary paper](https://www.numdam.org/item/ASNSP_2009_5_8_3_451_0.pdf).

The parent is right that DF has rank one on the boundary and that a Lipschitz inverse there is impossible: normal displacements t give image displacements O(t²). A “global spectral embedding” claim should always distinguish the open-domain diffeomorphism and one-dimensional boundary diffeomorphism from a smooth embedding of the closed domain.

No counterexample to the exact I214 statement is asserted here. No proof certification follows from this review. Nor do search misses prove worldwide novelty. The negative contribution decision rests on a positive comparison: established nodal-arc structure plus the accepted gradient theorem reduce the package to standard univalence and elementary radial/degree consequences. An exact prior publication remains unlocated.

## Reading and output boundaries

Full retained primary reading: Jones–Maggioni–Schul v4, all 45 pages/all 2,743 extracted lines; Bates v1, all 16 pages/all 784 lines; Braun–Llibre, all article pages 1–15 and PDF cover/back matter/all 754 lines. Bérard–Helffer v1 was read selectively by streamed text extraction, with exact ranges in the literature record; no full copy is retained or claimed read. Alessandrini–Nesi and other leads also have bounded reading recorded there. All pinned family text was read, but no upstream theorem was audited. Supplied I214 brief, report, analytic notes, literature and parent response were read as provided. I218 and other live reviews were not opened.

Only the three assigned output files and the three fully read primary PDF/text pairs in the assigned source directory were written. No research code, experiments, tests, scans, snapshots, seals, historical replay, shared/ancestor edits, staging, commits, subordinate agents or publication. Retrieval, text extraction and hash/JSON bookkeeping only. Authentication records and detached final hashes accompany this review.
