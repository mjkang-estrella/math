# RCS128 contribution review, recovery round 3

Original prose CC BY 4.0; code MIT. This is an independent contribution and eligibility review. It is not acceptance and does not change the count (12/20). Uploads are stopped.

**Verdict:** SUBSTANTIAL at the full, unchanged scope. Credit is narrowed to items 3, 5b and 6. Item 7's credit is withdrawn because of the Goldberg–Karzanov §5 splice. The verdict is conditional on RQ1–RQ5 in `review.md` §7.

Files:

- `review.md`: the verdict, the antecedents, the credit ledger, the R4 dispositions and the findings.
- `findings.json`: a machine-readable summary.
- `reading-limits.md`: exactly what was and was not read, and the checks run.
- `search-log.json`: the bounded web searches and fetches.
- `input-verification.json`: the input-packet and author-packet anchor, replay and controls.
- `opt_bruteforce.py`: an exhaustive OPT_RC check for the two motivating instances. It only prints to stdout.
- `verify.py` and `manifest.json`: an exact inventory seal. The caller must supply the external SHA256 of `manifest.json`. Run `python3 -B verify.py --anchor HASH` to verify. Add `--controls` to also run the positive, wrong-anchor and tamper controls, on temporary copies only.

Round 2 failed with a rate-limit error and produced nothing; that failure is preserved here as a fact. No third-party bodies are stored here. Nothing was staged, committed or uploaded, and no nested agents were started.
