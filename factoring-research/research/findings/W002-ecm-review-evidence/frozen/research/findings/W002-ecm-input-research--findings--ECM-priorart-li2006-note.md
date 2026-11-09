# Batch ECM: full-source gate after H030

2026-10-08. **Primary-art check completed; no new constructor selected.**
Verified COMPLETE factoring complexity improvement: **NONE**.

W001-dynamics Card 4 and the full H009 finding were reread. H009 rejects sparse
trimming on its registered sample; its characteristic-zero derivation remains
separately scoped and is not a universal modular lower bound. No H009 experiment
was replayed. H030's independently accepted exact-block obstruction concerns a
different computation and is not being transferred to ECM.

## Primary finding

Li's December 2006 dissertation, CERIAS TR 2006-43, is now archived in full.
Section 4.5 states O(m^2 log m) arithmetic operations for geometric evaluation,
and O(m^2 log^2 m) for arbitrary points. Section 4.6 reduces division-polynomial
recurrences modulo X^n +/- 1 for inputs N=s^n +/- 1. Theorem 4.6.2 states
O(k log m log n) arithmetic operations for k curves. These are source claims,
not a newly accepted bit-complexity theorem. The proof of Theorem 4.1.3 explicitly
assumes independence of curve-order smoothness events and uses approximations
to short-interval smoothness. Those assumptions are not removed by citation.
[Primary PDF](https://www.cerias.purdue.edu/assets/pdf/bibtex_archive/2006-43.pdf).

In the lab's notation m is the scalar K_B and log m is its bit-length scale.
Thus the cited special-form cost still multiplies curve count by scalar-length
work. This primary passage does not instantiate the desired additive B+r
primitive. Reintroducing cyclic reduction alone would duplicate known work,
even before supplying all bit costs and a useful-split probability.

## Exactness gate and scope

The printed plus-case identity (4.10) is restricted to odd i, while the
displayed evaluation list in Algorithm 4.6.1 includes all i from 0 to n-1.
Before reusing that algorithm, an explicit parity restriction or a different
annihilating modulus is required: s^n=-1 gives (s^i)^n=(-1)^i.
The read passages also contain a separate special Fermat reduction; it has not
been validated here. No claimed implementation behavior or whole-thesis
correctness conclusion follows from this limited check. We do not adopt its
probability or factor-return theorem as a proved input to the lab.

This closes cyclic parameter reduction as the proposed *new* escape from
H009. It does not rule out specialized input algorithms or a genuinely different
final-product computation. A bare resultant/norm notation supplies no such
algorithm: multiplicativity alone does not transport subtraction in the
division-polynomial recurrence. Any future norm-first proposal must give a
specific way to retain and compute the needed correlations with all setup,
intermediate widths, extraction and failed trials charged. No such recurrence
is supplied by this note, and no H032 task or numerical screen is selected.

## Reading and evidence

Downloaded the 69-page primary PDF successfully:
SHA-256 36180aa6bab0fa502efbb4ac0e27e41f055a1a5ffa5d3119d81b9841e3362185.
The title page identifies December 2006; inconsistent search-index dates were
not treated as publication dates. The text is a pdftotext -layout reading aid.

Read the table of contents and selected title/abstract material, Algorithm 4.1.1
on printed pp. 29-30, Theorem 3.3.1 and the start of 3.3.2's derivation on
pp. 24-26, Theorem 4.1.3 and adjacent argument on pp. 33-36, and all of
sections 4.5-4.6 on pp. 45-49. The latter five complete pages were rendered
and visually inspected (physical PDF pages 54-58). No full dissertation,
implementation, FFT precision, success theorem or source-code audit is claimed.

Only source retrieval, extraction, rendering, reading and evidence hashing ran.
No mathematical finite experiment, parameter search, solver, shared test or
Lean invocation occurred. The next live dependency is H031's independent review;
new construction selection remains open within the full research objective.
