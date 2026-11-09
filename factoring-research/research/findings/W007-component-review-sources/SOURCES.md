# Source snapshots for W007-component-review

Retrieved 2026-10-08 with curl into this fresh directory. The PDFs are untrusted
data. They were converted with `pdftotext -layout` and no code in them was run.
SHA-256 values are listed in `../W007-component-review-delivery.sha256`.

## Kowalski, "Exponential sums over finite fields: elementary methods"

- URL: https://people.math.ethz.ch/~kowalski/exponential-sums-elementary.pdf
- Title page: "Version of September 14, 2021" (kowalski.txt line 13).
- Read: Theorem 3.2 and the remark after it, printed pages 31–32
  (kowalski.txt lines 1679–1696).
- Statement used: for f in F_q[X] of degree d and a non-trivial additive character
  psi, if d < q and (d,q)=1, then |sum_x psi(f(x))| <= (d-1) sqrt(q).
- The remark right after it, on printed page 32, says the condition d < q is
  redundant because (3.3) is trivial when d >= q. The review uses this remark.
- The proof in Chapter 3 was not re-derived. The theorem is imported as stated.

## Cafure–Matera, Finite Fields Appl. 12 (2006) 155–185

- URL: https://bibliotecadigital.exactas.uba.ar/download/paper/paper_10715797_v12_n2_p155_Cafure.pdf
- Read: Section 2 definitions and Bézout inequality (7) (cafure-matera.txt
  lines 201–224), Lemma 2.1 and Lemma 2.2 (lines 225–262), the introduction's
  statement list (lines 170–196), and the statement of Theorem 5.2 (lines 872–876).
- Theorem 5.2: for an absolutely irreducible F_q-hypersurface H in A^n of degree
  delta, |#H(F_q) - q^(n-1)| <= (delta-1)(delta-2) q^(n-3/2) + 5 delta^(13/3) q^(n-2).
  The theorem has NO field-size hypothesis. The condition q > 2(r+1)delta^2 that
  the introduction lists belongs to the general-variety estimate, not to
  hypersurfaces.
- Lemma 2.1: an F_q-variety of dimension r and degree delta has at most
  delta q^r rational points. Here delta is the sum of the component degrees.
- (7): deg(V ∩ W) <= deg V * deg W, citing Heintz and Fulton.
- The proof of Theorem 5.2 was not audited. The review's main inequalities do
  not depend on Cafure–Matera. It is checked only as an alternative route and to
  scope the parent's citation.

## Input snapshot

- `input-W007-component-factorization.md` is a copy of the parent brief note as
  read at the start of this review.
