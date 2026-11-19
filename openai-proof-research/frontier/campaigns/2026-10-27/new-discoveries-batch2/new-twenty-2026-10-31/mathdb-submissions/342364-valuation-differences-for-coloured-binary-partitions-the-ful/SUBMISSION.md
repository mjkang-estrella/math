# MathDB 342364: Valuation differences for coloured binary partitions: the full Ulas–Żmija Conjecture 6.1 picture (even formula, odd bounds, sharpness, and failure of per-colour sharpness for m ≡ 15 mod 16)

- Problem: https://mathdb.com/p/342364
- Source: Ulas-Żmija arXiv:1904.03398 Conjecture 6.1; MathDB 342364
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `Ulas.Final5.full_theorem_E2 : EvenFormula ∧ OddOneBound ∧ OddThreeBound ∧ OddOneEquality ∧ OddThreeEquality ∧ FifteenBound ∧ NeverFifteen; Ulas.Final5.mathdb_342364 : ¬ Conj61 (per-k reading P1); Ulas.Final5.conj61_some : Conj61Some (some-k reading P2); all hypothesis-free`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `paper.pdf`
- Lean source: `ulas-source.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; not worldwide priority remaining_literature_limits: Żmija 2023 Acta Math. Hungar. body paywalled (abstract and references read); Google Scholar citation graph not checked; Crossref, Semantic Scholar and the arXiv search API not used trust_limits: Prebuilt upstream Mathlib oleans trusted; leanchecker shares the installation; upstream executable metadata and unused upstream axiom declarations inventoried separately not_claimed: Exact (iff) descriptions of the equality sets; Priority; Publication
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Proved: the full picture of the Ulas-Zmija conjecture on 2-adic valuations of differences between counts of coloured binary partitions: the exact even-case formula, the lower bounds +3 and +6 according to the parameter mod 4 with nonzero differences attained, explicit infinite equality families, and for the remaining residue a universal bound +7 so equality never holds. The conjecture is true under the some-k reading and false under the per-k reading. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Ulas and Żmija, arXiv:1904.03398v1 (Ramanujan J. 55 (2021) 623–660), Conjecture 6.1 on ν2(c_m(4n) − c_m(n)) for m-coloured binary partitions. Proved in full: the even formula ν2 = ν2(n) + 2ν2(k) + 3 for m = 2k; the bounds +3 (m ≡ 1 mod 4) and +6 (m ≡ 3 mod 4) with nonzero differences; explicit infinite equality families for m ≡ 1 (mod 4) and m ≡ 3, 7, 11 (mod 16); and for m ≡ 15 (mod 16) the universal +7 bound, so equality never holds. Hence the conjecture is false under the per-k reading and true under the some-k reading.

## Body (paste into the MathDB body field)

Use the written proof in this folder: paper.pdf. The complete Lean source is in ulas-source.zip.
