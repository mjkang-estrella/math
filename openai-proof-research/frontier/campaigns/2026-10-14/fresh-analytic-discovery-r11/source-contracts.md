# Source contracts

Author: Myeongjin Kang (no affiliation). Prose licence: CC BY 4.0.

## Pinned upstream

* Repository: https://github.com/openai/math
* Commit: `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` (sources/upstream.json,
  commit date 2026-10-08T05:20:00Z).
* Raw prefix used for every download:
  `https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Arithmetic-classification-and-non-Pisot-singularity-for-Bernoulli-convolutions-October-3-2026/`
* Catalogue family 153 (sources/CONTENTS.md). Manuscript: "Arithmetic
  classification and non-Pisot singularity for Bernoulli convolutions",
  OpenAI, October 3 2026.

## Files (private copies in inputs/private/source-153/, not redistributed)

All Git blob SHA-1 values were recomputed locally and match
sources/preprints-tree.json.

| path | git blob SHA-1 | bytes | SHA-256 | reading extent |
|---|---|---|---|---|
| README.md | fd1abc787eea89c1aa3a469c5a05cf1c7e939f34 | 1243 | d424bb87e55aea065c732431326db05fd9fdd456228fdc66f79d97649525935b | full |
| build/main.tex | 1fce7aad27ddf5f83680fb28a43f393d51756a55 | 9147 | 99878062e61cd5bc299afcb5f20181e87044a95616d1147d203ad4bcbefa232e | full |
| build/salem.tex | 68552edd50043c1bde3e54a891d3ef65a41c9b6e | 17489 | 6aba84f0a8b2fe51b1ca183c452cbdf1018da2f35499a95cf33217678a3636ea | full (read twice) |
| build/nonpisot.tex | 859f16285b1c270cfcc31336842044c48bd7ded5 | 26671 | e8d6e8537dc60f4142f629ac4c4e400efe74f6aed98a90f52630533b8955fb1a | full |
| build/classification.tex | 3abdd297813b3a2fd67c305468c0bc0e12fa59b6 | 27828 | adf8f2def37053838a980a052ffa9d37bfffc83a4953007cb8ec54ceae68712e | full |
| build/certificate.tex | 8630d0578a57a2e2a3900e5ed6d4aa45221caa10 | 28046 | 7d71cb685bcf4b33dd0ce8a9ae34dd0be0afdff28596d77f2515f5ee638ea47d | not read (np:main certificate; not used) |
| build/references.bib | 7222408828aec34147ab55ed77c7bb079e8581db | 7375 | 3b9dc5050d8a152abedf38b1494b49b2f9d8976dedb9b34446db41e3cb2aa3da | entries for Salem, Varju, Hochman, Breuillard-Varju, Baker et al., Kern-Sterk, Marshall-Maldonado-Solomyak |
| verification/verify_degree31.py | 8663aeacac2d9eadf2d0fe74f0bf125e27f50a68 | 20637 | 67eef9421933cb5eb32f717864d8badf0ad5836edf687fee36295cff18793dea | not read, not executed |
| paper.pdf | b95f2c9e8d112caccfc04124751959915d476688 | 566872 | n/a | not downloaded |

## Labels relied on

| label | file | statement used | role in candidate.md |
|---|---|---|---|
| sal:main | salem.tex | nu_{1/beta} singular for every quartic Salem beta in (1,2) | Comparison only; shows that degree four is paid. |
| sal:construction | salem.tex | multipliers with L_{m+1} >= 2.1 L_m; constraint k_{m+1} >= 2 b_m + D L_m | Exponent comparison in Section 4.2. |
| sal:loss | salem.tex | S_m = o(L_m); S_{m+1} <= (1+eta)(2+eta) S_m + C | Upper bound that matches the doubling (Proposition O2). |
| sal:trace | salem.tex | trace identity T_{m,j} in Z | Reproved inline for general degree (Lemma 4, Proposition O1). |
| sal:shift | salem.tex | u_{m+1,j} = u_{m,j+k} - u_{m,j-k} | Exact identity, reproved inline (Section 4.1). |
| sal:taylor | salem.tex | f(u+v) <= (1+eta) f(u) + C v^2 | Replaced by explicit-constant versions in Lemma 4 and Proposition O2. |
| np:main, np:integral, np:typical-gain | nonpisot.tex | degree-31 example; damping-product method | Read for method screening; not used. |
| cls:classification | classification.tex | arithmetic criterion | Read for screening; not used. |

No theorem in the candidate depends on the truth of a pinned theorem. The
pinned labels serve as comparison and as the source of identities that are
reproved inline.

## External primary literature (not pinned; only cited, method reproved)

See literature-screen.md. Cheng-Fang-Ma-Zhang arXiv:2610.12072v2, Lemmas 2.1
and 2.3, give the method of Lemmas 2 and 3. Those lemmas are proved in full in
candidate.md for general degree and are not assumed.
