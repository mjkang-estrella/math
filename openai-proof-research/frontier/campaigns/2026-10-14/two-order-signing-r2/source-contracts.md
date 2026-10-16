# Source contracts and reading extents (round r2)

Author: Myeongjin Kang, no affiliation. Original prose: CC BY 4.0.

All new deductions in `candidate.md` (Theorem 1, Proposition 3, Remarks 4–5,
Lemma 6, Proposition 7 and the failure analyses in §6) are proved there in
full. No proof in this round uses a third-party theorem as a step. The
sources below are used only for (a) the *status* identification in
Corollary 2 and §7, and (b) the lower bound C >= 2, which is Reis's
Theorem 142 (proof read in full; small cases replayed exactly by check R).
"Read" below means the stated extent was read in the local text extraction
and, where needed, checked against the PDF. Material outside these extents
was not read and nothing is claimed about it.

Local copies are private reading copies under `inputs/private/` and keep
their authors' rights. PDF text was extracted with `pdftotext -layout`
(poppler 26.01.0). The retrieval URLs, SHA256 values and sizes are also in
`retrieval-literature.json` and are bound by `input-manifest.json`.

## S1. Bansal, Rohwedder, Svensson, "Flow Time Scheduling and Prefix Beck-Fiala"

* URL: `https://arxiv.org/pdf/2202.02217` (retrieved file is v1, 4 Feb 2022).
* Copy: `inputs/private/literature/brs-2202.02217.pdf`
  (SHA256 `b9143f61b54d09f87bf481b33d5c0b85d096803fd7a6b74d5b0b0da9e998a627`).
* Read: all of §5 (PDF pp. 17–21): Definition 16 (the game), Lemma 17,
  Theorem 18, Definition 19 (weighted two permutation discrepancy C_n),
  Theorem 20, Lemma 21 with its full proof, and the §5.3 remarks. All of §6
  (PDF pp. 21–22), the SDP prefix-Komlós argument.
* Used for: Corollary 2(1) (D_2(1) = sup_n C_n, with the identity as the
  first order); §6 item 3 (Lemma 21 blocks the robust-game route); §6 item 5
  (one-order SDP context). Only the statements are used; none is a proof step.
* Interface: Definition 19 allows real values in [-1,1] with the first order
  the identity. Relabeling the indices so that pi is the identity and
  absorbing the signs of the scalars into epsilon gives exactly D_2(1).

## S2. Cherniavskii, Kupavskii, Moiseev, Shekhovtsov, "Approximation algorithms via discrepancy with hard constraints"

* URL: `https://arxiv.org/pdf/2610.16079` (retrieved file is v1).
* Copy: `inputs/private/literature/hardconstraints-2610.16079.pdf`
  (SHA256 `371c883306f8a8e54c3cb809220e999da0ee9067a6a9cb185c2a227977d8c228`).
* Read: §2.2 "Mountain distance bound" (PDF p. 7); statements of Theorems 4,
  5 and 6 (PDF pp. 7, 9); all of §6 "Conclusions and future directions"
  (PDF p. 18), including the paragraph "Weighted one-block matrices".
  Proofs of Theorems 4–6 were not read and are not used.
* Used for: Corollary 2(2) and §7 (U1): the question whether every matrix
  A_ij = d_j 1[i in I_j], d_j in [0,1], has constant hereditary discrepancy is
  posed as open there. Restricting columns keeps the same form, so the
  question is D_OB(1) < infinity. Theorem 1 converts it to D_2(1) < infinity.
  §6 item 1 cites Theorem 5 (via Newman–Neiman–Nikolov) only as context for
  three unrelated chains.

## S3. Reis, PhD dissertation (University of Washington, 2023), Chapter 8

* URL (recorded by r4): `https://digital.lib.washington.edu/server/api/core/bitstreams/a92e53bd-06e4-4b1d-9221-51ba75b0aded/content`.
* Copy: the r4 extraction `inputs/private/context/r4/inputs/private/literature/thesis.txt`
  (SHA256 `74e0271323eda68753966cec3a04cfd9558dd4f4bf8fd83e2ccfd83e3457bf8b`,
  equal to the r4 input-manifest entry; `verify.py` checks this). The PDF is
  not copied into this round.
* Read: Chapter 8, from Conjecture 16 through Theorem 144 (extraction lines
  about 6340–6560; thesis pp. 120–124): Conjecture 16, Claims 139–140,
  Theorem 141, Theorem 142 with Claim 143 and their full proofs, Theorem 144.
* Used for: Corollary 2(3) (Conjecture 16 and the TU/herdisc <= 1 remark for
  two-permutation prefix matrices); Corollary 2(4) (Theorem 142 gives
  D_2(1) >= 2, so C >= 2); §6 item 2 (Theorem 141's pairing idea).

## S4. Bérczi, Liu, Reis, Tarnawski, "Weighted Equitability and Matroid-Constrained Discrepancy"

* URL: `https://arxiv.org/pdf/2608.13983v1`.
* Copy: `inputs/private/literature/berczi-2608.13983v1.pdf`
  (SHA256 `1afa2f37c571d31b2936e157208e2a5b4891207d5ff26cbe7f0dfc61391ace75`).
  r4 separately bound the HTML version of the same v1.
* Read: §1 introduction and the statements of Conjectures 5 and 6 (PDF p. 6);
  §6 (PDF pp. 16–18): Lemma 12, Theorem 14 (O(log n) prefix bound),
  Proposition 15, Theorem 16. Proofs in §6 were skimmed, not checked, and are
  not used.
* Used for: Proposition 3 (the hypothesis is exactly Conjecture 5 as stated),
  and the context remark that Theorem 14 would give O(log N) at d=1 through
  the same embedding (not used).

## S5. Bansal, Nikolov, "Discrepancy Theory: An Algorithmic and Geometric Perspective"

* URL: `https://arxiv.org/pdf/2608.00140` (retrieved file is v1).
* Copy: `inputs/private/literature/survey-2608.00140.pdf`
  (SHA256 `81473b6d5e533168e00192a28604c121e7c4802280ff160c7d6a86d1d1f7bdc7`).
* Read: §2.3 "Discrepancy of Permutations" (PDF pp. 31–33), including the
  two-permutation bound 1 and Theorem 2.8 (k permutations, O(k log n)) with
  its proof; §7.5 "Prefix Discrepancy" (PDF p. 131).
* Used for: Proposition 7 is a self-contained vector adaptation of the
  Theorem 2.8 iterated-rounding idea (credited, re-proved); Remark 5 uses
  the unweighted two-permutation bound 1 only for context.

## S6. Screened, not relied on

* Liu, "Open Problems on Matroid Theory and Submodular Optimization",
  `https://siyueliu112.github.io/files/lecture-notes/Open_problems.pdf`
  (copy `liu-open-problems.pdf`, SHA256
  `fd08468af1f5fe15f9e6e024f75c2a3e047d168ec70e856a8866e2b759da4231`).
  Searched for "prefix", "permutation" and "Reis"; the hits (PDF pp. 1, 8–9,
  11, 14, 16) were read only to locate S4. Nothing is cited from it.
* Liu, Reis, "Weighted Chairman Assignment and Flow-Time Scheduling",
  `https://arxiv.org/pdf/2511.18546` (v1; copy `liu-chairman-2511.18546.pdf`,
  SHA256 `e7030254c2c42c08c66ad69ded271bf19e84f5dd95689c40f9b750636c32ada1`).
  Abstract and introduction screened; it treats one-order weighted prefix
  problems and does not address two arbitrary orders. Nothing is cited.

## S7. Inherited sources

The pinned OpenAI one-order signing theorem (`thm:signing`, upstream revision
recorded by r4) and the r4 sources (Knuth two-way rounding, MNT) were read by
r4 and are not re-read here. Remark 4 mentions the one-order theorem only to
say that at d=1 it gives nothing beyond the greedy bound, which Remark 4
proves directly. No step of this round depends on any of them.
