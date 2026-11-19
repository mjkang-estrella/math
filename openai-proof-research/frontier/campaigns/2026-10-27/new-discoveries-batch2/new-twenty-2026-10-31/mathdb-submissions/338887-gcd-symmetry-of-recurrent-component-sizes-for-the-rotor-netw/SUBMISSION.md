# MathDB 338887: Gcd symmetry of recurrent-component sizes for the rotor network on the bidirected cycle (Chan-Levine Conjecture 8.3)

- Problem: https://mathdb.com/p/338887
- Source: Chan-Levine arXiv:1804.03322 Conjecture 8.3 (Mem. AMS 2022); MathDB 338887
- Outcome: **PROVED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `ChanLevine.mathdb_338887 : for all n, m with [NeZero n], 3 ≤ n, 1 ≤ m, and i, j : ZMod n with gcd(gcd(n,m), i.val) = gcd(gcd(n,m), j.val): (∃! S, a component of a recurrent natural configuration of level m and weight i) ∧ RecurrentComponent (C m i) ∧ r n m i = r n m j; corollary recurrent_count_depends_only_on_gcd`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `paper.pdf`
- Lean source: `chanlevine-assembly-source.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; not worldwide priority remaining_literature_limits: AMS 2022 full body not freshly accessed (arXiv v1/v2 bodies read); citation coverage sparse; Google Scholar, Crossref, Semantic Scholar and the arXiv search API not used trust_limits: Prebuilt upstream Mathlib oleans trusted; leanchecker shares the installation; 64 upstream executable-metadata entries inventoried (not local, not axioms); the unique-existence predicate ranges over components with a recurrent natural representative; the identification with every Definition 4.8 recurrent component uses source Lemma 5.19 and is not packaged as a separate Lean theorem not_claimed: A standalone Lean equivalence between Definition 4.8 recurrent components and components of recurrent configurations; Distinct counts for distinct gcds; Priority; Publication
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Proved: the Chan-Levine conjecture for the rotor network on the bidirected cycle. For every n >= 3 and m >= 1, the number of recurrent configurations in the unique recurrent component of level m and weight i depends only on gcd(n,m,i); the component's existence and uniqueness are proved as well, in the source's network language. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Chan and Levine, Abelian networks IV. Dynamics of nonhalting networks, arXiv:1804.03322 v1/v2; Mem. Amer. Math. Soc. 276 (2022), no. 1358, Conjecture 8.3: for the rotor network on the bidirected cycle C_n, n ≥ 3, m ≥ 1, the number of recurrent configurations in the unique recurrent component C_{n,m,i} of level m and weight i depends only on gcd(n, m, i). Proved for all n ≥ 3 and m ≥ 1, in the source's network language, with component existence and uniqueness proved.

## Body (paste into the MathDB body field)

Use the written proof in this folder: paper.pdf. The complete Lean source is in chanlevine-assembly-source.zip.
