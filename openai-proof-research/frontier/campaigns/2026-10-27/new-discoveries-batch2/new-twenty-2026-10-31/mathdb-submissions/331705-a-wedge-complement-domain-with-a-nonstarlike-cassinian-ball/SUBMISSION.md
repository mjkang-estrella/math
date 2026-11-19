# MathDB 331705: A wedge-complement domain with a nonstarlike Cassinian ball

- Problem: https://mathdb.com/p/331705
- Source: R. Klen, M. R. Mohapatra, S. K. Sahoo, arXiv:1511.01298 Conjecture 4.7; Math. Nachr. 290 (2017) 1531-1543; R. Klen, arXiv:1603.00590 Section 2 strict-starlike convention; MathDB 331705
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `Cassinian331705.Wedge.ordinary_refutation : ¬ SourceClaim; Cassinian331705.Wedge.strict_refutation : ¬ SourceClaimStrict; Cassinian331705.source_refutation : ¬ SourceClaim (slit)`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `draft.pdf`
- Lean source: `331705-proof-source.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; not worldwide priority remaining_literature_limits: Math. Nachr. journal body unread (Wiley 403 not retried); Ibragimov 2009 body unread (predates the conjecture); Jia-Wang-Zhang 2021 body unread (client challenge); OpenAlex citing list screened only where arXiv bodies were accessible trust_limits: Prebuilt upstream Mathlib oleans trusted; leanchecker shares the installation; Exact apex supremum sqrt(17/10) and slit closed forms are ordinary supplements, not Lean endpoints not_claimed: Bounded-domain counterexample; Every literature definition of strict starlikeness; Priority; Publication
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: Klen-Mohapatra-Sahoo Conjecture 4.7, that every Cassinian ball in a starlike domain is starlike about its centre. The plane domain outside the closed wedge u >= 1, |v| <= (u-1)/20 is starlike about 0 in both the ordinary and the strict boundary-point sense, yet its Cassinian ball of radius 7/4 about 0 contains 4+i but not 2+i/2; the conjecture fails for every n >= 2 under the planar reading. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

U = C minus the closed wedge {u>=1, |v|<=(u-1)/20} is an open connected proper planar domain, starlike about 0 in both the ordinary and the strict boundary-point sense, yet its Cassinian ball B_c(0,7/4) contains 4+i and omits the midpoint 2+i/2. Klen-Mohapatra-Sahoo Conjecture 4.7 (every Cassinian ball in a starlike domain is starlike about the centre) is false for every n>=2 reading posed in the plane, under both the ordinary and the strict domain hypotheses.

## Body (paste into the MathDB body field)

Use the written proof in this folder: draft.pdf. The complete Lean source is in 331705-proof-source.zip.
