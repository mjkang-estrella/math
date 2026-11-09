# Preserved failures, deviations and limits

- **Unguarded commands (routing violation).** Early inventory `ls`/`wc`/`cat`/`grep` reads were native bounded reads. Three commands were not wrapped in the guard:
  - one `python3 -I -B -c` one-liner that only printed the top-level keys of the live `ledger.json`, before the guard script was read; it wrote nothing;
  - `cp -p ../../../../AGENTS.md admin-snapshot/ancestor-AGENTS.md` (an admin snapshot copy);
  - `mkdir`/`date` for lane setup.
  All later helper, Python, retrieval and hash operations were guarded.
- **AMS 404.** The first, guessed AMS PDF route for Borosh–Flahive–Rubin–Treybig returned HTTP 404 (`S0002-9939-1989-0953013-9`, a wrong article identifier). It was not retried. The correct identifier `S0002-9939-1989-0955458-1` was then taken from a web search result and fetched once (200).
- **Empty arXiv query.** The first arXiv API query, `au:Tyszka_A`, returned 0 results because of the query form. It was replaced by a different query, `au:Tyszka` (59 results). This was not a denial.
- **Withdrawn paper.** `https://arxiv.org/pdf/0911.0384` returned 404. Its abs page (200) says "This paper has been withdrawn" (v58). It was not retried; its content was not read.
- **Live NEXT.md moved.** After work, the live administrative `NEXT.md` hash differs from the snapshot taken at 07:53:46Z (root edits it). This is expected. The admin snapshot is not bound as a scientific input. Live `ledger.json`, `prior-campaign-context.json` and both AGENTS files were unchanged.
- **No denial routes touched.** No 403/429/challenge was observed. The denied routes (GitHub API/raw/codeload/diff/patch, ScienceDirect, Google challenge) were not contacted. No proxy, no TLS disabling, no browser.
- **Text-extraction limits.** pdftotext layout extraction damages exponents (for example 2^(n−1) appears as "2n−1"). Statements were checked against layout context, and the theorem statement and proof of BFRT were read in their entirety (3 pages).
- **Limits of the bridge's literature context.**
  - Not obtained: the MLQ 56 (2010) journal version of math/0702558, the Gomory 1969 original, and the Garfinkel–Nemhauser reference.
  - The Gomory step was re-proved independently (shortest-word argument), so the bridge does not depend on the unread items.
  - No citing-literature, MathSciNet/zbMATH or proof-registry sweep was run. The search cannot clear all history.
- **No Lean, manuscript, counts or nominations.** None were produced.
