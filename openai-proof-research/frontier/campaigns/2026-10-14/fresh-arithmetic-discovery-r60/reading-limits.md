# Exact provenance and bounded reading

This is a continuation of the same T019S59 scope, not a replacement target. The scope file is byte-identical to r59, SHA256 22e7466e2699457a0ee39e31f5ac1b982527f1a7b9115b2fa1c3bc7377a73d95. The external r59 manifest anchor is 9796d5d14fd04c32a298ed128381587df68107d69cec0c91ee13f9acc7493007; its copied manifest and proof-attempts are private historical context. They retain the earlier unresolved status.

Source pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb is stipulated. The complete canonical tree has13223 entries, truncated=false, SHA256 eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b. All32 non-PDF blobs in the three selected families are retained, with Git-blob hashes and SHA256 in `source-identities.json`; the47 complete family entries, including unretained PDFs, are in `source-family-inventory.json`. This is non-PDF source completeness, not a claim that source PDFs were retained or read.

## Source reading

Inherited actual reading from r59: exterior-sheet September24 all four mathematical sections in full; October6 section manuscript introduction and sections03–07 in full. In r60, section02 preliminaries was read in full as well. These supply the fixed valued fields/point, normal form, full-overlap patching, stable roots, arbitrary roots, realization and full-section comparison. Section08 global consequences is retained but was not read in full or used.

September24 section-manuscript mathematical files01–08 and figure are byte-identical to October6; its introduction was read in r59 and its full-body identity was checked. README, wrapper and bibliography differences were not fully analyzed. No global strengthening is inferred from their titles.

## Newly retrieved primary bodies

Exact URLs/body sizes/SHA256 are in `primary-identities.json`. Five new bodies supplement the seven retained r59 bodies. All PDFs and pdftotext -layout extractions are private. No primary is corpus-stipulated. The classical theorems are quoted at their precise hypotheses; full underlying literature proofs were not independently audited.

- [Mochizuki March3,2011 note](https://www.kurims.kyoto-u.ac.jp/~motizuki/Combinatorial%20Section%20Conjecture%20and%20Pop-Stix.pdf): all six pages/all301 extracted lines read, including finite cyclic graph fixed points, log-section argument, (*PTS), and compatible vertices/edges. The stated pro-Sigma surjectivity requires ell-cyclotomic fullness. Its nodally nondegenerate representation/semigraph dependencies were not fetched or audited independently.
- [Mochizuki May2,2011 note](https://www.kurims.kyoto-u.ac.jp/~motizuki/Comments%20on%20Valuations.pdf): all four pages/all187 extracted lines read, including both smooth-point limit-valuation and node-ray cases. This is the actual restricted-tower valuation construction, not an inference from the older November note.
- [Mochizuki Local Pro-p](https://www.kurims.kyoto-u.ac.jp/~motizuki/The%20Local%20Pro-p%20Anabelian%20Geometry%20of%20Curves.pdf): introductory notation and sub-p-adic definition, Theorem C, entire Section19 Theorem19.1/proof and following remarks (extracted5210–5307). Its pro-p diagonal-complement operation and earlier anabelian isomorphism dependency are credited. The roughly100-page paper's full anabelian proof was not audited.
- [Mochizuki Topics](https://www.kurims.kyoto-u.ac.jp/~motizuki/Topics%20Surrounding%20the%20Anabelian%20Geometry%20of%20Hyperbolic%20Curves.pdf): extracted2390–2450, Theorem4.12 and the following moduli-stack remark. This was a navigation/comparison route; the exact curve injectivity input is instead the preceding Local Pro-p Theorem19.1.
- [ABBR I v3](https://arxiv.org/pdf/1303.4812v3): Theorem6.18 statement (2158–2195), Corollary6.21 (2400–2433), full sections7.1–7.4 including classification proof/Remark7.5 (2435–2557), and Theorem7.7 with its full loop-subdivision proof (2572–2598). A portion of the proof of6.18 (2300–2350) was also read. The full proof of6.18, SGA lifting, and general tame covering theory were not re-audited. The fixed-gluing-datum criterion is used explicitly; it is false that7.4 automatically lifts every automorphism. ABBR II was a search lead only: the author-host fetch failed certificate validation and guessed arXivv2 returned404; no body from it is retained or used.

## Retained primary reading from r59

- Mochizuki–Tsujimura revised March30,2024: TheoremA/model formulation120–180; Proposition2.6/proof3083–3182; proof2.16 portion3660–3750; Theorem2.17/proof3840–3878. Earlier reductions and all surrounding proof bodies were not fully read. Its two-prime RNS scope is the input, while the prescribed model-domination application follows the source's operative interface.
- Pop MPIM2007/102: actual definitions, TheoremsA/B and elementary derived functoriality §2(A), extracted130–240. The full proof was not audited. The article appeared in Compositio146(2010),621–637; the 2010 publisher body and author's February2009 PDF were not successfully fetched here (author host403). No unverified version equivalence is claimed: the retained precise TheoremA is the cited input. Its statement covers finite p-adic fields containing mu_p, including p=2. The final proof explicitly checks that input and its quotient functor, rather than citing only an abstract.
- November2010 Mochizuki comments: full four-page note read in r59; retained for historical comparison, superseded by March/May in the proof.
- Pop–Stix arXivv1: ranges420–525,570–800,800–965,970–1233 as detailed in copied r59 notes. Its full-group localization is not used in place of the stronger March/May theorem.
- Stix period-index:285–323,370–435; r59 Brauer support only, not needed in the final proof.
- Hoshi May2010: introduction1–175, including pro-p counterexample statement setup and injectivity references. No claim that its nongeometric pro-p examples lift to Sigma-sections.
- Saidi2023: introductory conditions/TheoremA, first four pages as recorded in r59. Its metabelian/nilpotent-by-abelian quotients are not Pi_X^Sigma. Full proof not read.

The parent reports reading both March/May bodies, ABBR Cor6.21/§7 lifting and the current drafts, and independently checking the circuit characters and arbitrary-Sigma realization. These are collaborative author checks only. No pending independent review directory was read.

No numerical experiment verifies these theorems. Integrity replay authenticates bytes, exact inventory and source provenance, not mathematical correctness. All prose is original paraphrase except necessary mathematical notation. Original notes: Myeongjin Kang, no affiliation; prose CC BY4.0, verifier MIT. Primary bodies and source caches remain private. No staging, commits, uploads, shared-ledger edits or nested agents were made.
