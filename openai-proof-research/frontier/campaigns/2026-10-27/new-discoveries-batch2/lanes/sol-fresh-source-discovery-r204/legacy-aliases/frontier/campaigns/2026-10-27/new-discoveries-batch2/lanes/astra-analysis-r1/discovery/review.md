# Research handback: zero eligible new outcomes

## Decision

**Exclude MathDB 367221 / Zhou arXiv:2502.15173v4 Conjecture 5.8 from discovery
credit.** On the source's substantive ranges, both coefficient cancellations
are routine consequences of the already public Xu–Zhao
arXiv:2401.01385v2 **Lemma 4.4**. This is a demonstrated subsumption, not an
inference from a title, abstract, database status, or search silence.

The decisive chain is

    Cbar_(j,2)(pi/2)+Sbar_(j,2)(pi/2) = −4 A_(j−1)'(pi),
    A_(4s−1)=z^(4s)P_s(t(1−t)),
    A_(4s+1)=z^(4s+2)Q_s(t(1−t))(1−2t).

The first identity is elementary; the latter two are exactly the prior lemma.
One derivative at t=1/2 and Zhou's own source conversions give both conclusions.
See ../PROOF.md, especially sections 2–3. Original lemma and its entire proof
were read; the extracted text is ../sources/closest-theorem-excerpt.txt.

## Actual mathematical work

Before discovering this subsumption, I obtained an independent all-order
coefficient proof. For the transformed Jacobi function w, U=w'+w² solves

    U''=3U²−2(1+t)U−(1−t)².

Its centered equation has the symmetry V(v,1−t)=−V(iv,t). This implies the
exact parity and derivative vanishings of the canonical source coefficient
combination. PROOF.md section 5 gives the full proof, exact source polynomial
bridge, and all constants. This alternative argument receives **zero** credit.

The independently coded exact checker builds the original sn coefficients
from their cubic ODE, builds U coefficients from a different quadratic ODE,
and compares both after the source quadratic substitution. It passed for
p=2,...,12, with symbolic rational arithmetic. It also checks the Miura identity
and the first source examples. The finite check is not represented as a proof.

Five elementary Lean declarations compile with the prescribed absolute
Lean 4.34.1 binary and pinned mathlib package cache. Each reports only
propext, Classical.choice, Quot.sound. These are openly labeled **helper
checks**, not a certificate of the source conjecture. No `sorry`, `admit`,
new `axiom`, `unsafe`, or `native_decide` is used.

## Bounded live prior-art and revision screen

All accesses occurred on 2026-10-28 UTC (2026-10-27 Pacific).

1. [Zhou live abstract](https://arxiv.org/abs/2502.15173) gives v4,
   3 February 2026. [Actual v4 body](https://arxiv.org/html/2502.15173v4)
   retains Conjecture 5.8. Theorems 4.1, 4.3, 5.1, 5.4, source transformations,
   examples and endpoint remarks were inspected. The old Pi source was read
   and preserved, never modified.
2. [Live MathDB record](https://mathdb.com/api/posts/367221) is open with an
   empty solution/reply list. This was not treated as novelty evidence.
3. [Xu–Zhao v2 full body](https://arxiv.org/html/2401.01385v2) contains the
   decisive Lemma 4.4, and the actual proof gives the precise all-order
   polynomial symmetry. Its live abstract identifies v2 dated 18 January 2024.
4. [Xu–Zhao 2301.08211v2](https://arxiv.org/html/2301.08211v2) and
   [their reciprocal-hyperbolic-series paper](https://arxiv.org/html/1801.07565)
   were also retrieved. The theorem lists, relevant sum structures and
   coefficient conjectures were compared; no need to rely on these more
   distant endpoints once Lemma 4.4 was found.
5. Actual companion bodies
   [Gu–Xu–Zhou 2506.20074v2](https://arxiv.org/html/2506.20074v2) and
   [Chen–Xu–Zhou 2510.16041v1](https://arxiv.org/html/2510.16041v1) were read
   for definitions, structural theorems, coefficient claims, and references.
   Neither was used to clear novelty based on an abstract.
6. The live Semantic Scholar citation response for 2502.15173 listed two
   entries (2506.20074 and 2505.05545). This index is incomplete: the second
   companion was located separately. The 2505.05545 full body was not needed
   or read. No exhaustive citing-body coverage is claimed.
7. Ideosphere's public landing/catalog HTML was retrieved and searched for
   Berndt, 2502.15173, and 367221, with no match. This covers that retrieved
   page only, not the entire service. The name Zhou occurs in unrelated work.
8. Complete recursive public trees for google-deepmind/formal-conjectures
   and the-omega-institute/trureturing were retrieved (neither truncated),
   and their filenames screened for Berndt/Zhou/367221/15173/elliptic.
   No relevant filename was found. This is a bounded filename screen, not
   content search of every repository, and not evidence of absolute novelty.
9. Web searches used the exact paper title, arXiv identifier, combinations of
   Zhou/Berndt/conjecture/coefficients, and site:ideosphere.ai and
   site:github.com restrictions. No explicit posted resolution was located.
   This negative observation is weaker than, and superseded by, the actual
   prior-theorem subsumption.
10. The actual Corollary 33 in Waldschmidt's author-hosted
    [Transcendence of periods account](https://webusers.imj-prg.fr/~michel.waldschmidt/articles/pdf/SurveyTrdceEllipt2005.pdf)
    states algebraic independence of pi and Gamma(1/4). This confirms the
    coefficient-uniqueness ingredient in the short subsumption proof.
    The original Chudnovsky paper was not separately retrieved; the alternate
    canonical-coefficient proof avoids this ingredient entirely.

## Limits and strongest objections

* **Fatal eligibility objection:** the proof is a routine corollary of the
  actual earlier Lemma 4.4. Neither a different ODE proof, a future complete
  Lean certificate, nor individual parameter cases would remove this.
* **Source endpoint:** the f formula is stated for m>=2. The source separately
  evaluates m=1 with an extra −pi/8. No discovery or counterexample is claimed
  from the conjecture's imprecise m>=1 wording.
* **Full formal gap:** no Lean implementation connects the infinite sums,
  Jacobi polynomials, and source c/d/e/f coefficients. The saved helper module
  does not hide or fill these bridges. Full formalization was intentionally
  stopped after the eligibility failure.
* **Publisher access:** direct Zhou ScienceDirect request returned 403; MDPI
  reciprocal-series request returned 429, and was not retried. Full arXiv
  bodies were available. The MathNet PDF link for Nesterenko redirected to
  its homepage; the original article body was not read through that link.
* **No priority certification:** search indexes and the two repository trees
  are bounded. The exclusion does not depend on asserting any first author
  explicitly wrote the final coefficient relations.
* **No external posting:** no messages, account mutations, uploads, or git
  actions were made. All new artifacts are in this assigned lane.

## Other initial lead and handback

The predecessor analysis lane had no saved proof. Its Toda candidate already
had a full public counterexample; Schoenberg was explicitly described as
proved. They were not reinvestigated as new discoveries. The Szarek–Wolff
2410.15118 source was briefly retrieved as a backup; no theorem, counterexample,
novelty clearance, or exclusion is claimed for its Schatten-norm questions.
The discrete lead and root's Ku work were not duplicated.

Root alone decides ledger changes. This handback proposes **zero** acceptance
credits and no provisional new-result candidate.
