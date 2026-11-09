# Validation and reproducibility

All new files are in this lane. No git, child agent, shared-ledger edit, upload, external message or browser tab was used. Dependencies were read only. No Lean theorem is claimed and no dummy formal packet is supplied.

Python scripts set CPU and address-space resource limits for expensive calculations. They were launched with `timeout 140`; CPU limits are 120 seconds. Node jobs use `ulimit -t 120`, 2 GB old-space heaps and an address-space ceiling to allow V8 reservations. BLAS jobs use one OpenBLAS and one OMP thread. Enumeration/state caps are recorded per output. Shell sessions are foreground managed calls, not detached jobs. The final process check is retained separately.

`bootstrap.py` extracts exact raw JSONL lines with original newlines. `extracted.json` binds original corpus chunk, one-based line, raw and chunk SHA256. `results.json` adds statement-UTF8 hashes. `scripts/fetch.py`, `registry.py`, and `additional_sources.py` retain URL/time/status/content-hash receipts. The sole initial HTML 404 was for the grid source, which was subsequently read through its PDF; no denied route was retried. arXiv search, Crossref, MathDB/Palomar and ScienceDirect were not queried.

Live registries were fetched only through `/commits/HEAD` to choose revisions, never `/commits/main`; immutable tree SHA endpoints were used for complete D5/Problems listings. Registry path screening is not proof-body or novelty clearance. The OpenAI default HEAD matched the previously bound snapshot. Keyword path hits containing “nac” inside “Fibonacci” are not same-object proofs.

Reproduce a calculation from this lane with, for example:

```
PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 timeout 140 python scripts/algebra.py
PYTHONDONTWRITEBYTECODE=1 timeout 140 python scripts/pf_symbolic.py
PYTHONDONTWRITEBYTECODE=1 timeout 140 python scripts/wcs_large_unary.py 501 511
PYTHONDONTWRITEBYTECODE=1 timeout 140 python scripts/nac_exhaustive.py
```

For Node, use the same CPU/heap/address-space caps as the retained commands. `scripts/search.js stack 9 5 START END` selects disjoint slices of the 120 explicitly generated patterns, using zero-based patterns. Its source example uses the literal human labels 231.

Python exact integers, rational polynomial arithmetic and Sturm calculations are reproducible ordinary computations, not Lean certificates. Floating point spectral checks have tolerances and cannot certify exact inequalities. The snake Sturm test certifies only the computed h* polynomials; its correspondence with source objects has not been formally verified in Lean. Source snippets are text conversions retaining math alttext; original HTML/PDF hashes remain authoritative.

The C++ prototype was never executable because g++ is absent; the failed attempt is preserved in `logs/stack-9-4.txt`. The independent JavaScript implementation supplies the actual stack/word outputs. A missing BeautifulSoup dependency was resolved by a standard-library HTML parser, with no package installation. No full upstream rebuild or cached-mathlib trust assertion is made.
