# Functional hard-sphere fluctuations: N1-N7 consolidation

These consolidated bytes await parent/focused review. The prior full-scope manuscript PASS applies only to the frozen `kinetic-manuscript/` input. No gate, acceptance, campaign count, submission, or upload is advanced here. `kinetic-release/` still binds the old paper and was not changed.

The paper retains the actual unsmoothed deterministic gas on R3 x R3, excluded-product grand-canonical law including N=0, mu=epsilon^-2, H's exact kinetic hypothesis on the whole supplied regular lifespan, exact microscopic centering for every finite list of real compact smooth tests, and J1 convergence plus C-tightness. H is stipulated at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.

## Files

- `main.tex`, `references.tex`, `output/pdf/main.pdf`: consolidated paper (19 pages).
- `original-to-consolidated.diff`: exact unified TeX diff against frozen original.
- `response-to-review.md`: N1-N7 disposition and exact current locations.
- `source-map.md` / `.json`: 25 claim groups and current labels/lines.
- `source-sections.json`: authenticated H shorthands, actual section order and titles.
- `inputs.json`: original dependencies, every frozen package file, review files, and antecedent note; project-root-relative hashes and lengths.
- `outputs.json`: all final package deliverables except itself; `hashes.json` records TeX/PDF/diff/input hashes.
- `qa/page-01.png` through `qa/page-19.png`: final all-page renders. `qa/visual-qa.json` and `qa/portability-check.json`: current QA receipts.
- `history/`: untouched original author documentation/QA receipts, explicitly historical.
- `provenance.md`: attribution, current read scope, frozen input bindings, limits and release status.

## Reproduction

Run commands only in this directory or a disposable copy:

```sh
python3 build.py --tectonic /tmp/frontier-typeset/tectonic
python3 verify_sources.py --project-root /path/to/openai-proof-research
python3 verify.py --project-root /path/to/openai-proof-research
python3 verify_outputs.py
```

Both source and structural verifiers parse explicit `--project-root` before any root discovery and support arbitrary-depth copies. Without it they find ancestor `AGENTS.md` and `sources/upstream.json` markers or issue a clear argument error. The source verifier can use `--fetch --project-root /nonexistent` for temporary pinned retrieval without modifying shared sources. Rebuilding changes PDF metadata/hashes; rerender, inspect every page and refresh the output manifest for any new build. The input manifest authenticates frozen dependencies; it does not authorize writes to them. The output verifier is read-only and intentionally detects changed build bytes.

The inherited repair/adversarial/editorial controls are finite support only. The nine separately compiled Lean declarations remain scoped algebraic support; no full geometric, analytic or stochastic theorem is formalized. Author: Myeongjin Kang; no affiliation. Original prose/paper CC BY 4.0, original code MIT; third-party rights and notices unchanged.
