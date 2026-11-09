# r133 frozen statement (frozen 2026-10-20T17:21:32Z, before proof drafting)

Author: Myeongjin Kang (no affiliation). CC BY 4.0. Runner provenance: Factory Droid / claude-opus-5-5 / high.

## Theorem (Brannen's reverse projection inequality for 4-polytopes with at most six facets)

Let K be a convex polytope in R^4 with non-empty interior and at most 6 facets. Let ΠK be its projection body,
h_{ΠK}(u) = V_3(K | u^⊥) for unit vectors u. Then

    V_4(ΠK) <= (160/3) V_4(K)^3,

and equality holds if and only if K is a simplex. (160/3 = (n+1) n^n / n! at n = 4.)

Scope: only polytopes in R^4 with at most 6 facets. No claim is made about general convex bodies in R^4, about
polytopes with 7 or more facets, or about dimensions 5..8.

## Prefreeze disclosure

Before this freeze the following were done (all recorded in work/notes.md): reading of the briefs, r132 materials,
FHLX (I43-retained text, in full), Source P main.tex (in full), CONTENTS entry 088, a project history search;
float explorations (B-spline evaluations, HNBUE bound, (S)_n suprema); exact sign-pattern polynomial certificates for
the auxiliary inequality (S)_4 (scratch/cert.py, all ten patterns, nonnegative coefficients); a literature check
(arXiv abstract page of 2610.13953, Saroglou arXiv:1409.4347v2 HTML introduction and references, two web searches;
Saroglou 2011 Mathematika PDF fetch failed on TLS verification and was not bypassed). The proof sketch (reduction,
HNBUE comparison, (S)_4) was known at freeze; the full written proof is drafted after this freeze.
