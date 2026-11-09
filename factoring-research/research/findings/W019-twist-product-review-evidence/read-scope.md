# Frozen sources and exact read scope

Evidence ledger for `../W019-twist-product-review.md`.
All writes are confined to that report and this evidence tree.
No solver run, Lean action, package installation, delegation, commit, or
shared-state edit was performed.

Python was used for snapshot hashing and for the one preregistered
class-number program. Poppler (`pdfinfo`, `pdftotext`, `pdftoppm`) was
already installed and was used only to read primary PDFs. The PDF skill was
read for the read-only extraction workflow. No PDF was authored.

## Repository inputs

`input-freeze.json` records the snapshot path, byte count, and SHA-256.
Copies were made before the audit conclusions were written. After the
certificate run, every live source file still matched its snapshot.

Read completely:

- AGENTS.md, RESEARCH_TEAM.md, RESEARCH_LOOP.md, README.md,
  docs/SPECIFICATION.md
- research/hypotheses/W019.md, all 232 lines. Only section C was audited.
  Sections A and B were not judged.
- research/hypotheses/W017.md
- research/findings/W017-character-batch-review.md

W004.md has 168 lines. Lines 1–80 were read, through the proposed two-field
selector and the definition of `f_i`. The remainder was not read. A file
search for class-number, Euler-product, and annihilator language found no
such hypothesis. W004’s conclusions were not used.

`brief.txt` is the review assignment. `research/STATE.md` was not read and
was not needed for section C.

## Primary sources

Retrieval URLs, sizes, and PDF hashes are in `source-retrieval.json`.
Full PDFs and `pdftotext -layout` transcripts are archived. Archiving is
not a claim that every page was read.

### Schoof, Quadratic fields and factorization

PDF SHA-256
`d58c6b9f73b1bfc1a17735f52fa62a25b32e361a2c0fc8bd04896e0eef15e7d3`.
Printed page = PDF page + 234.

Visually inspected renders:

- p. 244, formula (4), the abelian class-number formula. The composition
  formulas on the same page were not used.
- p. 245, imaginary class-number formula, the w=2 reduction, the informal
  GRH truncation sentence, and the finite maximal-order sum.
- p. 246, the finite-sum continuation, the reduced-form counting sentence,
  and the discriminant -691 example used only for its boundary sign.
- p. 264, the `N^{1/5+ε}` GRH factoring statement and the ambiguous-form
  definition.
- p. 265, ambiguous-form factorizations and the sentence that finding one
  costs about as much as computing the class group by the section 3
  strategy.
- p. 266, Theorem 6.1 and Corollary 6.2.
- p. 267, Theorem 6.3 and the opening of its proof through the contour
  integral of `L'/L`.

The bibliography pointers [1] Borevich–Shafarevich and [17] Lang were read
from the `pdftotext` transcript. Neither book was opened. The proof of
Theorem 6.3 was not finished. Its reduction from nonfundamental
discriminants to fundamental discriminants was not audited. Reference [15],
Lagarias–Montgomery–Odlyzko, was not opened. The running-time argument for
the `N^{1/5+ε}` bound was not reproved.

### Lemmermeyer, Kuroda’s class number formula, Acta Arith. 66 (1994)

PDF SHA-256
`ba3d048d68d59278dd1ba84b19142de37ffbbb557b49f929166fc6ad4e759679`.
Printed pages 245–260.

The opening of p. 245 was read from the transcript. Printed pp. 246–247
were visually inspected, including the norm map `j`, formulas (1.1)–(1.5),
and the three special cases over Q. The first lines of the proof of (1.2)
on p. 247 were seen. The rest of the proof, Furuta’s genus formula, and the
later examples were not audited. Walter, Herglotz, Kuroda 1950, Kubota, and
Hilbert were not opened. Lemmermeyer’s warning that Walter’s formula can
fail when the eighth roots of unity lie in K was read as a warning, not
rechecked.

### Benjamin, Lemmermeyer, and Snyder, Pacific J. Math. 230 (2007)

PDF SHA-256
`04510902ab2cd73f2eb831ab58ed4d07460a9abb56b32e6038beb0c7043d7c0a`.
The PDF opens with the journal cover. Printed pp. 27–28 were visually
inspected: Dirichlet’s quartic formula, the multiquadratic formula, the
definition of ν, and the statement that the unit index q is the obstruction
and has no general explicit formula even in degree 4. The values of q
displayed on p. 28 were read as evidence that q is not universally 1 or 2.
The later case-by-case genus-field computations were not audited. Wada 1966
and Kubota 1956 were not opened.

## Certificate

`class-number-certificate-preregistration.md` and
`class-number-certificate.py` were hashed into
`class-number-certificate-freeze.json` before the only execution.
The program exited 0 within the 60-second limit. Its output is
`class-number-certificate-results.json` and
`class-number-certificate-run.log`. No edit and no second run followed.
The program performs a few hundred arithmetic operations, below the
20,000-event ceiling. It does not test Euler tails or factor integers.

## Arguments owned by this review

Proved here: the unramified Euler identity, the square-conductor character
identity, the coprime fundamental-discriminant product, the group-ring
characterization of coefficient vectors, and the exponent arithmetic in the
relaxed cost model.

Cited and not reproved: Dirichlet’s theorem; Schoof’s class-number
formulas, reduced-form bijection, Theorem 6.3, and the `N^{1/5+ε}`
algorithm; Lemmermeyer’s formula (1.5); the Benjamin–Lemmermeyer–Snyder
multiquadratic formula and unit-index statements.
