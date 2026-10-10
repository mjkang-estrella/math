# I113 immutable discovery evidence

The report is `frontier/iterations/i113-online-optimization-discovery.md`. It nominates no substantial finding and leaves the accepted count at eight. P113 is an author-level technical robustness deduction; R113 remains open. G113 is a technical exact-output reduction.

This directory owns snapshots, exact lexical search expressions/multisets, the 10,373-position I88 mapping, 94 selected pinned references, current primary version/retrieval records and reading-passage hashes. Originals from I14/I79 and four existing primary PDFs/texts from I22 are referenced by immutable identity. No corpus was copied or recursively downloaded. The complete preprint tree has 13,223 entries and 749 manuscript directories. Only the four live ledger originals listed in inputs.json may drift; none of their snapshots may drift. No I110/I112 working output is bound.

Corpus search and pinned passage numbers use decoded UTF-8 (replacement on invalid bytes) and Python `str.splitlines()`. External PDF-text passage numbers use splitting on literal LF, so form feeds are preserved inside lines. A passage hash is over selected decoded lines joined by LF, without an extra trailing LF. These conventions are intentionally different. The three new PDF extractions were performed only during discovery with `pdftotext -layout`; the 776 inherited corpus PDF texts and I22 texts are never re-extracted during verification. Identity does not certify extraction accuracy.

`prepare_evidence.py` is a discovery-time manifest builder, not the verifier. `diagnostics.py` uses exact fractions on finite cases only. `verify.py` is offline and read-only, checks an exact owned inventory and all immutable references, and has no download/write/extraction/bytecode/repair/reseal operation. Run from any directory with the absolute verifier path, or from the repository with:

```
PYTHONDONTWRITEBYTECODE=1 python -B frontier/experiments/i113_online_optimization_discovery/verify.py
```

The final seal is a one-time inventory envelope and cannot hash itself. Every other owned file, including the verifier, report, diagnostics and preseal validation history, is bound by that envelope. Replaying it does not establish a universal theorem, substantiality, priority, formal proof or independent human review.
