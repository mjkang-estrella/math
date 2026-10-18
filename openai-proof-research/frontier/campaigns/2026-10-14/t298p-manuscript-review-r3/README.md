# T298P independent full manuscript review, round 3

Verdict: **NEEDS_REVISION**, with an explicit local score-pairing repair and formal trust-disclosure completion in `review.md`. The full frozen theorem scope is retained. This package makes no acceptance, count, or worldwide novelty decision.

The manuscript source/PDF is unchanged. A fresh isolated build reproduces its PDF byte-identically; all 18 pages were rendered and inspected. Exact source/reading limits, formal coverage and required-versus-optional findings are in `review.md`, `reading-extents.md` and `verdict.json`. Receipts are under `checks/`; temporary PDF/PNGs are excluded under `tmp/`.

Obtain the manifest hash from the external handoff, then run the read-only verifier:

```bash
python3 -I -B verify.py --anchor EXTERNAL_MANIFEST_SHA256
python3 -I -B verify.py --anchor EXTERNAL_MANIFEST_SHA256 --repo /path/to/openai-proof-research
```

This checks bytes and exact membership; it does not prove the review or the theorem. The second command also rechecks 171 external file digests. All non-tmp payload files are sealed. The manifest itself requires its externally supplied anchor. No symlink or multiply linked payload file is permitted.

Independent finite convention diagnostic and copied-tree verifier controls:

```bash
python3 -I -B check_pairing.py
python3 -I -B verify_controls.py --anchor EXTERNAL_MANIFEST_SHA256
```

The controls write only this directory's tmp/ and delete their copies. They check one positive case and eight failures, confirming the verifier writes no files. A preliminary-seal control receipt is included; final-seal controls were replayed to excluded scratch to avoid a circular sealed receipt.

To repeat the isolated manuscript build after reading its build script:

```bash
python3 -I -B ../t298p-manuscript-r1/build.py --output tmp/another-fresh-build --tectonic /path/to/tectonic
pdftoppm -r 115 -png ../t298p-manuscript-r1/output/pdf/main.pdf tmp/page
```

`audit_inputs.py` rechecks supplied manifests and their listed payloads, original author-bound input hashes and canonical generator blobs, reruns the inspected read-only input verifiers and finite arithmetic, and collects receipts in this review only. It expects the existing `tmp/rebuild/` produced by the review's fresh build. It does not run Lean or make a mathematical verdict. Re-executing it changes receipts and requires resealing; normal read-only verification uses verify.py instead.

No third-party full paper is redistributed. Original reviewer code/prose is provided as review evidence; it does not relicense the input author, source or formal packets. Reproduction trusts the installed Python/Poppler/Tectonic tools and TeX bundle; formal compilation was not rerun in this manuscript review.
