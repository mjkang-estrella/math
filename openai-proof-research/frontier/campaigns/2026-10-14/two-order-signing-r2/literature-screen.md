# Literature screen (round r2)

Author: Myeongjin Kang, no affiliation. Original prose: CC BY 4.0.

Bounded primary check, 2026-10-16. Goal: find whether T2 or its d=1 case is
stated, proved, refuted or posed as open in primary sources, and which
two-order machinery exists. This is not an exhaustive search. A missed source
remains possible.

## Starting point inherited from r4

r4 screened Knuth's two-way rounding, Reis's weighted-discrepancy chapter,
Matoušek–Nikolov–Talwar (gamma_2 / trace norm) and Bérczi et al. (HTML v1).
Those findings are retained. This round re-read the relevant part of Reis's
Chapter 8 from the r4 extraction (see `source-contracts.md`, S3).

## Web queries issued (verbatim)

1. `weighted discrepancy two permutations prefix constant bound wdisc herdisc conjecture`
2. `"prefix-constrained" bases matroid weighted two chains discrepancy two permutations open problem`
3. `Bansal Rohwedder Svensson "Flow time scheduling and prefix Beck-Fiala" two permutations weighted`
4. `"weighted two permutation discrepancy"`
5. `two permutations weighted discrepancy constant bound proof 2025 2026 arXiv prefix sums both orders same signs`
6. `"two permutation" discrepancy weighted Rohwedder OR Reis OR Nikolov 2024 2025 constant bound real weights`
7. `"2-sparse prefix Beck-Fiala" constant bound resolved`

One direct fetch was attempted
(`https://siyueliu112.github.io/files/lecture-notes/Open_problems.pdf`). It
failed as a PDF, so the file was retrieved with `curl` instead. All primary
files were retrieved with `curl -sSL` from the URLs in
`retrieval-literature.json`.

## Findings

* **BRS 2022 (S1).** Definition 19 defines weighted two permutation
  discrepancy, which is exactly D_2(1). Theorem 20 bounds only the {-1,0,1}
  case. Lemma 21 shows that the natural robust online game cannot give a
  constant. The weighted question is left open.
* **Reis 2023 (S3).** Conjecture 16 (wdisc < 2 herdisc) would imply D_2(1) <= 2.
  Theorem 142 gives D_2(1) >= 2. Theorem 144 concerns 2-sparse prefix
  Beck-Fiala. No upper bound for weighted two permutations is given.
* **Bérczi–Liu–Reis–Tarnawski 2026 (S4).** Conjecture 5 (prefix-constrained
  bases) implies D_2(1) < infinity by Proposition 3 of `candidate.md`.
  Theorem 14 gives O(log n).
* **Cherniavskii–Kupavskii–Moiseev–Shekhovtsov 2026 (S2).** §6 poses the
  weighted one-block question as open and asks for a direct proof. By
  Theorem 1 of `candidate.md`, this is the d=1 case of T2.
* **Bansal–Nikolov survey 2026 (S5).** Two permutations (unweighted):
  discrepancy 1. k permutations: O(k log n). No weighted constant bound.
* **Liu notes and Liu–Reis (S6).** Screened only; they locate S4 and treat
  one-order weighted prefix problems.

No source found states T2 for d >= 2, or for d = 1 with a constant bound.
No source found refutes it. Queries 5–7 returned nothing beyond the sources
above that resolves the weighted case.

## Consequence

The d=1 case of T2 is a recently posed open problem (S2, October 2026) that
was singled out earlier (S1, S3). The screen does not establish that T2 for
general d has never been considered; it establishes only that its d=1 case
is open in the sources read.
