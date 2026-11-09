# Source gate — 330695 (binary maximality of distinct abelian-square factors)

Gate executed 2026-11-05T21:00–21:40Z. Verdict: **PASS → bounded diagnostics permitted.**
No material source hold remains; no known proof or refutation of the conjecture was found.

## 1. Literal statement (verified in both known versions)

> "If a word of length n contains k distinct abelian-square factors, then there exists a
> binary word of length n containing at least k distinct abelian-square factors."

- arXiv:1506.03562v1 (Fici–Mignosi, 2015), **Conjecture 1**, §4 — cached r253
  `http/1506.03562.txt` l.596–598, sha256 24628919… (frozen, verified).
- Journal version **arXiv:1701.00948** "Abelian-Square-Rich Words" (Fici, Mignosi,
  **Shallit** — three-author journal revision), **Conjecture 27**, §6 — fetched 2026-11-05,
  `receipts/http/1701.*`; Conjecture 27 at extracted l.925–926. This is the TCS 2017
  (DOI 10.1016/j.tcs.2017.02.02 **012**) body per Unpaywall (bronze OA, publishedVersion
  S0304397517301299). The quantifier is over ALL finite words on ARBITRARY alphabets;
  distinctness is on literal factor strings (the paper counts "distinct abelian-square
  factors", deduplicated by content, not by Parikh class — its §5 distinguishes the
  Parikh-equivalence variant as a *different* count, Conjecture 28).

## 2. Access record (single attempts; no retries of denied resources)

| resource | result |
|---|---|
| api.unpaywall.org DOI record | 200, `receipts/http/unpaywall-tcs2017.json` |
| arXiv 1701.00948 abs/pdf/e-print | 200, saved |
| sciencedirect.com published PDF | **403 once** (html challenge); not retried; body read via the author arXiv camera submission instead |
| Semantic Scholar citations graph | 200, 8 citing works, `receipts/http/sstcs2017-citations.json` |
| api.github.com HEAD re-fetch for receipts | 403 rate-limit (unauthenticated); heads already verified 21:08Z: openai `4eaee875…`, omega `5ea4a916…`, pool `01db1d70…` — all equal to the r253 `prior_screen` values, so the registry is current and contains no newer proof |

## 3. Printed examples / tables read (routine-copy exclusions noted)

- Table 1: Thue–Morse ASFF first values; §3 2-regularity proof (journal §4/5).
- Table 2 + Examples 15/18: Fibonacci-word length-6 factors, AS_n(F) values.
- Corollary 1/2: Sturmian lower bounds fab(n) ≥ n−1. None of these is a binary-maximum
  theorem; none is eligible as a 330695 endpoint.

## 4. Prior/successor clearance (bounded, not a novelty claim)

All 8 Semantic-Scholar-indexed citing works screened by abstract (2018–2026, IDs in
receipt): none states a proof or refutation of Conjecture 27; 2605.19535 (closed-rich
constant), 2509.20773 (mutually abelian-bordered), 2008.08125 (abelian closures),
2112.05347 (2-binomial complexity), 2107.09206 (detection hardness), 2207.09937 = the
2022 survey already in r253. The survey's Conjecture 11 (Mäkelä: every *binary* word of
length n has ≥ ⌊n/4⌋ distinct abelian squares) is a lower bound in one alphabet — a
different question. Omega `FazekasAbelianSquareEqualityRefutation.lean` (r253 cache) is a
lower-bound equality refutation, not this maximum-over-alphabets statement.

## 5. Triki 1907.05369 — gap re-confirmed from full text

`abelian2019.txt` (frozen): Lemma 1 + proof induct by extending w only by a **copy of its
last letter** (`wx, x equals the last symbol`). An arbitrary length-(n+1) word is not of
this form; and the claim that a non-factor last letter gives k+1 is asserted, not proved.
The two-page proof therefore does not cover all extensions: an identified gap, not a
resolution.

## 6. Conclusion

Gate passes: primary body + all known versions + printed examples + successors + registry
heads cleared. Bounded diagnostics authorized and executed (see SUMMARY.md). No
obstruction (witness beating the exact binary maximum) was found for n ≤ 20, hence **no
Lean endpoint is claimed**; the endpoint plan is in SUMMARY.md §5. This document does not
assert complete literature clearance beyond the checks listed.
