# Reading and scope — R1 support audit

Date: 2026-10-14. Assignment: independently supply the compact-p regularity interface required by I345; no new-result credit.

Read project AGENTS.md; the complete Opus `p-gradient-proof/review.md`, with particular attention to R1 and Section B; and the complete I345 analytic report, first §§1–6, then §§7–11. The I345 reading/failure ledger was also read to identify the historical Uhlenbeck pages 5–8 gap. This round does not change that earlier ledger or the Opus review's actual reading history.

The parent supplied the full primary PDF `/tmp/frontier-typeset/uhlenbeck.pdf` and its layout extraction. The PDF SHA256 matches the assigned `bb041a82ffd0b1c7e1b694a162aac642c2755dfd3bf00726e443ac8106e7239a`. Both source files are copied under `sources/` for persistence; no fresh network retrieval is claimed. Original URL: https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6219-11511_2006_Article_BF02392316.pdf .

Read the complete extracted Sections 1–5, including the previously unread PDF pages 5–8 / journal pages 223–226. Also read the introduction and Theorem (6.1) proof; the latter is context and not necessary to the new compact-parameter deduction. Formula-dependent passages were revisited in bounded output calls after the initial broad output was truncated.

Rendered and inspected the following primary pages where OCR was ambiguous:

- p. 221 / PDF page 3: precise (1.3), (1.3)' and (1.4), including the placement of the exponent s−a and the fact differentiability is required only for Q>0.
- pp. 232–235 / PDF pages 14–17: the nonlinear error bound, half-ball comparison, the excess contraction and reference-vector iteration. A higher-resolution p. 232 rendering was inspected for the Taylor-comparison paragraph. The support proof defines the true flux Taylor remainder explicitly and derives its comparison energy estimate, rather than relying on the printed G normalization; its linearization is the matrix in (4.2), with the factor 2.
- p. 238 / PDF page 20: exact two parameter inequalities in (5.4), and `sqrt(1−lambda)=4^(−gamma)` in (5.5).

Additional p. 230, 237 and 239 renders are retained as nearby source context. They were not needed to resolve further OCR uncertainty after the bounded text readings.

`lemma.md` explicitly distinguishes source facts from the new **uniform choices**. In particular:

1. Common structural K and continuity exponent are proved for the power family.
2. The opaque power-map constant in the source is replaced by an explicit uniform inverse comparison. A common flux Taylor bound and a fixed Sobolev exponent prove a common small-excess gain.
3. Reference size eta is fixed as 1/2, and its iteration lower bound 1/4 is paid by an explicit drift budget.
4. The perturbation radius/excess and final decay factor are chosen once, with formulas.
5. Caccioppoli and a common reading of (3.2) supply the oscillation-to-gradient bound; there is no dependence on Kotschwar–Ni in this support lemma.
6. The critical-gradient branch uses the repeated maximum decrease; it never linearizes at a zero gradient. Dimension two uses a constant third-coordinate extension.

No separate classical paper's proof, no pinned-source truth audit, no full I345 re-review, and no contribution/novelty verdict is claimed. No computation or finite experiment is substituted for the parameter-uniform analytic argument. No Lean formalization is claimed. Writes were confined to this assigned directory; no prior evidence, index, git state or publication destination was changed.
