# H017: a bound calculation is not a root-extraction algorithm

Status: primary-source scope check, 2026-10-08. No improved ECDLP algorithm,
numerical experiment, installed package or new Lean claim.

Primary source: Feng, Luo, Chen, Nitaj and Pan, *Computing Asymptotic Bounds for
Small Roots in Coppersmith's Method via Sumset Theory*, CRYPTO 2025, pp.3–32,
[published PDF](https://link.springer.com/content/pdf/10.1007/978-3-032-01855-7_1.pdf).
Root read the introduction, §2.4, Theorem1 and §5.2/Theorem2. Native Sol independently
retrieved the same publication; its candidate analysis remains in progress.

The source proves asymptotic lattice dimension/determinant calculations using
sumsets. Its §2.4 Assumption1 still requires the reduced polynomials to define a
zero-dimensional variety. Lemma12 needs both modular vanishing and a scaled
coefficient norm below modulus/sqrt(number of monomials) to infer integer
vanishing. Theorem2's exponent0.2599 concerns two specified CSURF hidden-number
polynomials and retains Assumption1. It is not an ECDLP or Semaev-polynomial root
bound. Theorem1 also has support/index hypotheses. These restrictions remain
when using the authors' [bound-calculation code](https://github.com/fffmath/AsymptoticBounds).

## Research gate

This resolves the previous inaccessible-PDF gap, not the missing attack. Any
H017 candidate must specify the actual equations, integer lifts, monomials,
normalization and finite lattice schedule; verify the norm certificate; and
justify extraction of useful roots and useful relations at the claimed cost.
Cheap construction of determinant formulas alone supplies none of those paid
operations. Polynomial independence is a separate assumption, not a custom
attack axiom to install in Lean. An unsuccessful chosen schedule would not
exclude other schedules or coordinate-aware algorithms.

The next decision is whether the independent small-root proposer can supply
a valid schedule whose complete extraction/collection/rank costs could beat
the accepted square-root reference. No lattice implementation is approved by
this source note alone.

## Exact retrieval evidence

Web open returned an internal access error for the publisher PDF. Terminal
retrieval succeeded (exit0), followed by text extraction (exit0):

```sh
curl --fail --location --max-time 25 --silent --show-error 'https://link.springer.com/content/pdf/10.1007/978-3-032-01855-7_1.pdf' -o /tmp/h017-small-roots.pdf
pdftotext -layout /tmp/h017-small-roots.pdf /tmp/h017-small-roots.txt
rg -n 'Assumption|Theorem|Commutative|independen' /tmp/h017-small-roots.txt
sed -n '740,825p' /tmp/h017-small-roots.txt
sed -n '860,945p' /tmp/h017-small-roots.txt
sed -n '1550,1670p' /tmp/h017-small-roots.txt
```

Source PDFs/text remain temporary and are not staged. No source timing is a
local measurement, and no package code was executed.

Repository validation: `./scripts/check.sh > /tmp/ecdlp-h017-source-check.log
2>&1` from dlp-research exited0; all363 existing dependency audits passed.
No Lean definitions or theorem claims changed, so Audit.lean is unchanged.
