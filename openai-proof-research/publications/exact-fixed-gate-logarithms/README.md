# Exact discrete logarithms from a flagged polygonal transform

Myeongjin Kang, Independent researcher.

Assume the flagged polygonal-transform and exact-factoring interfaces specified in the paper. We construct a polynomial-time uniform quantum circuit family over one fixed finite gate set that computes discrete logarithms in prime fields with probability one and polynomial worst-case resources. For prime-order inputs, each verified Fourier-bin label has probability at least 1/(81q). Given its verified logarithm, that probability is computable exactly by a bounded number of lattice-point counts in dimension at most thirteen. Dyadic completion produces success probability exactly one quarter, followed by one exact amplification step. All sampled probabilities are dyadic; no input-dependent rotation or postselection is used.

6-page English preprint. Compile `main.tex` with Tectonic or pdfLaTeX. The source ZIP contains standalone `main.tex` and was rebuilt in an empty directory.

Final PDF: `output/pdf/exact-fixed-gate-logarithms.pdf`. Source ZIP: `output/exact-fixed-gate-logarithms-arxiv-source.zip`. Publication metadata is in `metadata.json` and `mathdb-entry.json`; audit reports and repair disposition are in `evidence/`.

Research pin: `mjkang-estrella/math@d513e308d86a38004d78bab9b9e88532e92bf56c`. Upstream pin: `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

License: All rights reserved. Claude Opus 5.5 manuscript audits and the parent repair check are AI reviews, not human peer review or formal verification.

Zenodo: https://doi.org/10.5281/zenodo.23350041
