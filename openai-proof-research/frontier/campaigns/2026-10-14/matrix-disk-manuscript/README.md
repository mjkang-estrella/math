# Attained complete polynomial disk rigidity: manuscript package

Author: **Myeongjin Kang**, no affiliation. Date: 2026-10-14.

`main.tex` and `references.tex` form a standalone 11-page manuscript; the compiled deliverable is [output/pdf/main.pdf](output/pdf/main.pdf). Its mathematical proof is self-contained relative to the explicitly credited pinned complete-Crouzeix/Faber operations and Jin's Lemma 8 and Proposition 6. It includes the dimension-independent exterior convergence and residual extraction in full, rather than citing an internal PASS as a proof.

The exact scope is every finite base dimension, coefficient dimension, and polynomial degree, with base-first evaluation and actual positive-maximum factor-two attainment. The active-block theorem also supplies fixed coefficient spaces, a polynomial unitary channel of unrestricted positive rank, its decaying rational exterior inverse, and a full determinant level set. The full numerical range is recovered after the active-block argument.

The frozen discovery proof passed independent proof review, and the separate bounded primary-literature gate returned SUBSTANTIAL for **one** package. This new manuscript presentation awaits independent review and parent integration. This directory does not accept a result, increment a campaign count, assert worldwide priority, or record a public upload. At preparation the campaign ledger records R023 as its only new accepted result (1/10).

## Reproduce

From this directory, with Tectonic 0.17.0 (the session binary is `/tmp/frontier-typeset/tectonic`):

```sh
/tmp/frontier-typeset/tectonic --keep-logs --outdir output/pdf main.tex
pdftoppm -r 105 -png output/pdf/main.pdf qa/page
pdftotext -layout output/pdf/main.pdf qa/main.txt
python3 checks/discovery/check.py
python3 checks/reviewer/supplemental-check.py
python3 validate.py
```

The final TeX build has zero warnings and no unresolved references. All eleven rendered pages were inspected. The 17 discovery checks and 16 independent-review supplemental checks pass in exact arithmetic, including deliberate mutation rejections. Both scripts are unchanged copies with their source paths and hashes recorded. They support finite identities; they are not proofs of the analytic limit, Fatou step, geometric input, or full theorem. No full Lean certificate exists. A separate finite scalar real Markov formalization being prepared elsewhere is not represented as a verified artifact in this package.

## Files and provenance

- `source-map.md` and `source-map.json`: source-to-statement/equation map, including the four presentation requests.
- `provenance.md`, `inputs.json`, `publication-metadata.json`: author/license instructions, frozen proof/review identities, exact read extents and external access limits.
- `checks/`: byte-identical supporting programs and regenerated exact output records.
- `qa/page-*.png` and `qa/main.txt`: all-page visual QA and PDF text extraction.
- `validation.json`: reproducible structural/typesetting/finite-check validation plus explicit human-readable inspection record.
- `outputs.json`: inventory with SHA-256 hashes of every package file except the manifest itself.
- `LICENSE-paper.txt`, `LICENSE-code.txt`: CC BY 4.0 for original paper/prose, MIT for original code. Third-party source rights remain intact.

No upstream manuscript or third-party primary-source text is redistributed here. Public references use immutable OpenAI revision URLs or explicit external versions. The archived Jin excerpt is identified as an attributed extract, not as a freshly retrieved full-source copy. Supporting source scripts retain their bytes and any existing notices. The source map distinguishes mathematical premises, reproduced inherited arguments, new bridge deductions, and literature comparisons.

The only remaining manuscript gate is independent review of this presentation. Broader priority, journal peer review, full analytic formalization, and public submission are not certified by these files.
