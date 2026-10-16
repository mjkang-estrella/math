# Focused manuscript revision audit r2

Verdict: **PASS_REVISION**, no required fixes. See `review.md`; the optional stale scratch-location wording is nonblocking. Author Myeongjin Kang, no affiliation. Original prose CC BY 4.0, original code MIT; third-party rights retained.

This is the explicitly T3-owned independent manuscript/revision-readiness gate. It does not recertify the historical mathematical proof PASS, award campaign acceptance, change the count, certify priority or provide a full Lean certificate.

Reproduce independent checks from this directory, using Python 3.9 or later:

```sh
python3 -B checks/audit_inputs.py
python3 -B checks/check_verifier.py
python3 -B checks/check_attribution_algebra.py
python3 -B checks/audit_inputs.py --after
```

`check_verifier.py` uses disposable extractions under `work/` and deletes them on completion. It does not import or modify author code. It executes the inspected verifier in frozen read-only mode and in isolated mutated copies. Full fixed repository inputs must be available for the full-mode positive control. The script expects the exact externally pinned r2 package.

The independent PDF rendering command was:

```sh
pdftoppm -r 120 -png ../kn-minus-edge-manuscript-r2/main.pdf qa/page
pdftotext -layout ../kn-minus-edge-manuscript-r2/main.pdf qa/main-layout.txt
pdfinfo ../kn-minus-edge-manuscript-r2/main.pdf > qa/pdfinfo.txt
```

All 15 final page renders were visually inspected. `qa/visual-review.json` records pagination, margin and build-log evidence. No Lean, TeX, release-checker or long mod-p rerun was performed. Existing exact sources and receipts are identified honestly as historical evidence.

`input-manifest.json` references inputs in place and is not a redistribution grant. `output-manifest.json` excludes itself and `SHA256SUMS`; the latter covers the output manifest as well. Neither includes disposable test copies. Run results and full verifier transcripts are in `receipts/`. The full review was saved before these output manifests were sealed.
