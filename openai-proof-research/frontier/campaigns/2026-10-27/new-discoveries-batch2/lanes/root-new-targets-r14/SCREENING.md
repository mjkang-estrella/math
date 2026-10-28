# Root screen r14 — 28 October 2026

No credit. Total remains 32/60. This lane preserves exploratory work and
distinguishes a source-index correction from a substantive new theorem.

## Hermitian Jacobi source: latest version and correction

Kuijper arXiv:2607.25760 has v2 dated 20 October 2026, newer than the July
version underlying MathDB 376316–376318. The actual v2 PDF was downloaded,
and pages 30, 34 and 36 rendered and visually read. In that PDF equation (21)
defines the product family, Definition 3.5 the operator, and Conjecture 3.13
the surviving rectangular-partition eigenfunction claim. Do not reuse the
old all-partitions conjecture: the author already gives a counterexample to
it. The strong-triangularity question is now Proposition 3.14, with a proof.

`jacobi_small_probe.py` directly transcribes the matrix-entry differential
operator using eight independent entries. In the m=2,k=2,kappa=(1,1,1) case,
let C=I-A and

    Q=det(B)-tr(B adj(C))/2+det(C)/3.

The exact calculations give GQ=-10Q. The literal product for
tau1=(1,0), tau2=(1,1) is P=(tr(A)-4/7)Q, and

    GP+18P=-(4/7)Q != 0.

Replacing 4/7 by 1/2 makes the residual identically zero. This matches the
missing matrix-dimensional shift in the source's beta marginal parameters:
integrating a 2x2 Hermitian B with 0<B<I-A contributes det(I-A)^2 to the
marginal density. The corresponding a1 increases from 4 to 5 in this example.
This is an apparent **parameter-index correction**, not a discovery nomination.
No full corrected theorem, independent review, literal Lean endpoint, or
priority claim is made. The source also contains derivative-index typographical
issues; the checker uses the consistent alpha,beta derivative convention from
the HTML and the intended generator, not an unbound-index reading of the PDF.

## Percolation implied Poisson parameters

Gladkov arXiv:2408.08457 latest v2 (22 August 2024), Conjecture 10.2, is a
retained lead (MathDB 364374). A bounded numerical probe enumerates every one
of 32768 configurations of K6 and computes edge connectivity as the minimum
over all terminal cuts. It then evaluates 601 independent edge-probability
vectors (including zeros/ones representing subgraphs), testing 2282 usable
adjacent Poisson-parameter comparisons. No negative gap was found; the smallest
observed gap was 0.013508599394205055. Floating probability arithmetic and
inverse incomplete-gamma evaluations are reconnaissance only, not a theorem,
an exhaustive parameter check, or a novelty gate. No exact certificate exists.

## Other reconfirmed limits

- Finite-free p-Stam 374150/374151: the previous campaign already performed
  degree 3–5, p<2 searches with no counterexample. No duplicate search or
  proof claimed. The present source copy is retained as a reference only.
- Bergman–Rubin 359807: latest 2309.02047v2 retains the generalized Erdos–Lax
  conjecture (now Conjecture 2). No resolution obtained. The all-unimodular
  result and the exterior integer-exponent case are already theorems.
- Segura 364320: earlier r23 already searched the meaningful higher hierarchy
  through order 40 with no counterexample. The obvious first-order scope
  inconsistency is uncounted; no duplicate proof effort made.
- Talla Waffo 373215: arXiv2602.16761 now v4; the revised body has no labelled
  conjecture. No proof-level disposition of the old smallest-zero question
  inferred from that text search alone.

Primary URLs/hashes for downloaded PDFs are in retrievals.json. Live arXiv
history pages were read. No external messages, uploads or database edits.
