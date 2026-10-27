# Final-review journal-body access record (pi-mills-cm-final-review)

## Prior state (frozen)
source-access-r2/attempts.json: four canonical PDF routes (www.ams.org/journals/...,
pubs.ams.org/...) returned HTTP 403. Unpaywall (fresh/unpaywall.json): only OA
locations are the arXiv submittedVersion via HAL hal-04382024 (no deposited file);
no published-version OA copy exists in any repository.

## NEW successful route (this review)
- AMS full-text HTML article view (genuinely new URL form, not among the four
  attempted PDF routes):
  https://www.ams.org/journals/tran/2023-376-02/S0002-9947-2022-08748-1/viewer/
  HTTP 200, 11,826,259 bytes, full published Transactions body in HTML with
  MathJax TeX copypaste spans (saved: fresh/ams-viewer.html).
- The viewer HTML embeds the canonical PDF permalink
  https://www.ams.org/tran/2023-376-02/S0002-9947-2022-08748-1/S0002-9947-2022-08748-1.pdf ;
  fetching it still returns a cookie-consent HTML shell (fresh/tran-8748-published.pdf),
  so the PDF bytes remain unread, but the HTML full text IS the published body.

## Published-body verification (from fresh/ams-viewer.html)
1. Published definition: r(x) = e^{x^2/2}\int_x^\infty e^{-t^2/2} dt — exact match
   to the manuscript's literal Gaussian tail.
2. Published Conjecture 3 (aria-label of the display formula):
   "z right arrow from bar minus StartFraction (r^(n)(z))^2 Over r^(2n+1)(z)"
   i.e. z |-> -(r^(n)(z))^2 / r^(2n+1)(z), "For every integer n" — plain z
   argument, n = 0 included. EXACT match to arXiv v2 p.31 and to the formal
   SourceConjecture351688 / sourceRatio n=0 bridge.
3. Published CM convention: "Throughout the paper, the CM property will be
   implicitly meant on (0, infinity)" — matches SourceCompletelyMonotone on Ioi 0.
4. Published Proposition 10 (aria-label): z |-> -(r^(n)(sqrt z))^2/r^(2n+1)(sqrt z)
   — square-root input; the counterexample does not contradict it.
5. Published section 5.5 "The case of Mill's ratio" and Conjecture 3 as an open
   problem are retained in the published version; pages 855-890 confirmed.

CONCLUSION: the material journal-source limit is RESOLVED for the exact question.
The published statement matches the preprint statement; no scope or priority
obstacle from the published body remains.

## Other fresh evidence (this review)
- fresh/mathdb-351688-final.json: fresh MathDB GET 200; status open; ALL of
  solutions/model_attempts/human_solves/formulations/attachments/comments/replies
  empty; lean_formalization_count 0.
- arXiv abs page: v1 2021-08-20, v2 2022-05-19 (latest) — v2 confirmed latest.
- fresh/unpaywall.json: no published-version OA anywhere.
- fresh/openalex-fresh.json + citing query: cited_by_count 3, exactly the three
  retained citers (bessel 2026 PJM, unimodal 2025 Results Math, fox 2026 H-functions).
- fresh/2512.04940.pdf/.txt: same-author follow-up read in full; cites [FS23] only
  as comparison-inequality framework reference; no Mills content; no resolution.
- fresh/cambridge-meixner.pdf/.txt: Sakuma-Ueda Canad. J. Math. 2025 read; open
  access; cites [FS23] only for beta-gamma algebra background; free-probability
  content; no Mills content; no resolution.
- fresh/yang-higher-order.html: 2026 J. Inequal. Appl. higher-order monotonicity
  paper: Y_{a,b}(x) = (x^2+a)R^2 + bxR; does not cite Ferreira-Simon; different
  expressions; no conflict with the counterexample.
- arXiv 1305.5429 (Gasull-Uzet, withdrawn): proves r itself CM; no conflict.

## Observation (nonblocking)
sources/fox2502.10483 (one of the three OpenAlex citers) does NOT cite
Ferreira-Simon anywhere in its body or reference list (checked full text);
the OpenAlex linkage appears erroneous. Novelty screening is unaffected (absence
of citation implies absence of resolution), but "three citers" should be read as
"two real citers plus one erroneous OpenAlex link."
