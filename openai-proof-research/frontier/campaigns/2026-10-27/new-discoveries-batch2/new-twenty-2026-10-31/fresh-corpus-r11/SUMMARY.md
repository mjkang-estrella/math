# fresh-corpus-r11 — final research handoff

**No new solution or Lean endpoint survives this lane. Zero credit claimed; shared counts unchanged.**

All 40 reserved literal normalized records were extracted and read. `extracted-records.json` preserves each complete raw line, its line number and SHA256, and the containing chunk path and SHA256. `results.json` is keyed by every reserved ID and separates literal review, primary statement review, selected proof-body review, ordinary mathematics, diagnostics, exact gaps, formal completion, and novelty limits.

Review depth: 40 literal records; 9 endpoints with selected relevant primary proof bodies read, 3 more with primary statements/definitions read, and 28 reviewed at literal-record level only. Thirteen primary PDFs are retained, including two Bajnok–Matzke companions. Downloading a paper is not represented as reading all its proofs. No major formalization was started for source-excluded or unproved endpoints.

The substantive attempts and ordinary deductions are in `MATHEMATICS.md`:

* **331205:** product-set obstruction tested in 7,669,491 bounded parameter combinations; then nine non-product MILP subset optimizations with independently recomputed exact witness difference sets. No violation. Stabilizer reduction identifies the remaining aperiodic, exponent-sensitive small-doubling obstruction. No finite or universal theorem certified.
* **331781:** proved the valuation-parity reduction: at n=2^g+1 the predicted answer is the squarefree part of W(n), so W(n) equals the prediction times a square. Primes above sqrt(n) are completely determined. Integer diagnostics for the remaining primes at g14,15 match. The decisive unproved lemma is sparse-row valuation <=1. This is useful analysis, not a full conjecture proof or novel helper credit.
* **331222:** worked through a coordinate-avoidance proof over fields and identified exactly why it fails over general rings with zero divisors. Finite/countable cases are already in the source. Full arbitrary-ring endpoint remains open in this lane.
* **331342:** compared the source's adding-a-path determinant proof against actual subdivision; deletion of the old edge parameter prevents the stated submatrix/noncancellation argument from carrying over. No rank-preservation proof obtained.

Source-based exclusions prevent wasted formal work: **331135** is proved in Haverkort Lemma6 and the concluding paragraph; **331888** is the exact source Theorem1.6; **331996** substitutes degree-bounded b-matchings for the source's edge-colorable subgraphs; **331546** swaps symmetric nu and skew eta; the **331537** ordinary-graph counterexample route is an explicitly known domain case. The h1 signed-sumset shortcut is also barred by the source's global h>=2 assumption.

`receipts.jsonl` gives dated primary-download hashes. Current Palomar queries returned403; no later requests or alternate routes were used. No MathDB denied route was retried. `access-limits.json` records this failure and the unexecuted C++ diagnostic (compiler absent). A recent OpenAI public repository-head receipt is reused with local hash verification in `registry/reused-head-receipt.json`; this is a bounded head observation, not subject-specific novelty clearance. Published/later-source leads from web search are documented in `source-search-notes.md`; abstract inspection is distinguished from body review. No empty-hit inference or worldwide-priority claim.

No Lean files, standalone acceptance packet, strict extracted replay, or transitive axiom audit are claimed, because there is no proven viable endpoint to certify. All scripts, sources, diagnostics and failed routes remain local to this assigned directory. No git, publication, contacts, browser tabs, shared edits, or subagents.
