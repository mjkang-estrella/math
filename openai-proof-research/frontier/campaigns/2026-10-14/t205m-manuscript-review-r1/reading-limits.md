# T205M manuscript review r1: reading limits

What this review did not do, so that its PASS is not read more broadly than
it is.

1. **Upstream truth.** The pinned OpenAI sources (revision
   `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`) are a premise by project rule.
   I checked that the five cited labels exist in the pinned private copies
   (`dominance.tex`, `band-quotient.tex`, `path-band.tex`) and that their
   statements match Proposition 2.1 (i)-(iv), including the constant `c_m` and
   the full induced quotient for `s in {1,2}`, `h=m-s>=1`. I did not audit the
   proofs of those source results.
2. **KSS.** I independently downloaded arXiv math/9901037v1 (byte-identical to
   the packet's primary copy) and read Section 2.1-2.2, (2.4)-(2.6) and
   Theorem 2.10. I verified the specialization to column rectangles and the
   absence of a string-length cutoff. I did not re-prove Theorem 2.10 or read
   Section 4 beyond the cited Definition-Proposition label.
3. **Kirillov.** I did not re-read arXiv hep-th/9304099v2. Every Kirillov-derived
   quantity used in Lemma 5.1 (maximal configuration, its vacancies, its weight,
   the one-cell move) was rederived directly from the KSS formula as stated in
   the manuscript, so the citation is context rather than a load-bearing gap.
4. **Literature.** I did not run a fresh priority search. Novelty statements are
   checked only against the manuscript's own claim boundary and the sealed
   contribution review (SUBSTANTIAL, narrow; new to this project, not shown new
   to the literature).
5. **Finite computations.** My recomputation (`independent_finite.py`) is
   reviewer-written and uses different algorithms from the author's code, but
   it is still a computer calculation run once on one machine (Python 3.14).
   `lemma_controls.py` checks lemma *statements* at a few orders beyond the
   finite starts; it is evidence only and is not used as proof of any
   all-order step.
6. **Formal support.** I did not rebuild the Lean support. I relied on the
   sealed scoped formal review (PASS_SCOPED_T205M) and checked only that the
   manuscript's description of it (17 declarations, 2 definitions and 15
   theorems, support only) matches the sealed packet copies.
7. **Rendering.** I rebuilt the PDF with tectonic 0.17.0 and inspected all 13
   pages at 110 dpi. Inspection is visual; I did not proofread every glyph of
   the bibliography against publisher records.
8. **Parent preflight and earlier replays.** I did not rely on the parent
   preflight or on the author's and manuscript agent's finite replays. Every
   identity, build, and finite result in `review.md` comes from my own runs.
9. **Acceptance.** This review changes no campaign count, ledger, or
   acceptance state. Those decisions belong to the parent.
