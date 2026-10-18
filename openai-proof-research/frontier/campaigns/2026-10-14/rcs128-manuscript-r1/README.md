# RCS128 complete manuscript r1 — author-side

Full 17-page source-relative article, unchanged frozen theorem, pending independent manuscript review. Count remains 12/20; this packet makes no acceptance or release claim. Uploads remain stopped.

- Public article: `public/output/pdf/rcs128.pdf`; original LaTeX: `public/article.tex` and `public/sections/`.
- Reproducible build: `public/build.py`; logs and successful receipt: `validation/final-build/`; byte-identical copied-source build: `validation/copied-source-build/`, `validation/reproducibility.json`.
- Every page rendered: `validation/pages/`; actual visual reading: `validation/page-inspection.json`.
- Complete findings mapping: `response-to-findings.json`; frozen §§1–7 and scope mapping: `proof-scope-crosswalk.json`.
- Input anchors: `input-identity.json`; exact direct reading and limits: `reading-provenance.json`; metadata audit: `bibliography-audit.json`.
- Development build errors preserved under `development/build-01` through `build-04`; checkpoint states their resolutions.

Read-only verification requires the external manifest SHA256 supplied in the handoff:

```sh
python3 verify.py --root /absolute/path/to/this-packet --anchor EXTERNAL_SHA256
```

It checks exact file and directory inventories, bytes and sizes, rejects symlinks (including root and ancestors), hardlinks, FIFOs and other nonregular nodes. It does not run mathematical checks or infer truth from hashes. `development/seal_controls.py --root PACKET --anchor SHA256` runs fourteen controls on disposable copies outside the frozen packet and checks that original bytes are unchanged. `development/seal.py` is an authoring tool and must not be used to validate changed bytes against the historical anchor.

The manifest hashes all payload files and lists every directory, excluding only itself. The external anchor is deliberately not stored as a self-authentication claim inside the manifest. The final handoff anchors all bytes; any subsequent change requires a new reviewed version.

Original prose CC BY 4.0, code MIT, Myeongjin Kang (no affiliation); see `public/LICENSE.txt`. Existing private third-party sources are referenced only by path and hash and are not copied into this packet. Full packet contains build logs and page renders; the public subtree contains only the original article, source, build script and rights/readme material.
