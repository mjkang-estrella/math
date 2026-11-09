# The crossing number of the complete graph minus an edge

Myeongjin Kang, no affiliation. Manuscript draft dated 2026-10-16.

`main.pdf` (15 pages, built from `main.tex`) proves:

- **Theorem A.** For every integer n >= 2 and every edge e of K_n, the ordinary crossing number is cr(K_n - e) = Z(n) - C(floor((n-1)/2), 2) = (1/4) floor((n+2)/2) floor((n-1)/2) floor((n-3)/2) floor((n-4)/2). All ordinary drawings are allowed.
- **Corollary B.** For all m >= 4 and n >= 1, with P_n the path with n edges, cr(K_m □ P_n) = (1/4) floor((m+1)/2) floor((m-1)/2) floor((m-2)/2) (n floor((m+4)/2) + floor((m-4)/2)). This is one application of Theorem A through Ouyang–Wang–Huang 2014, Corollary 5.1, which is cited and not re-audited.

The proof uses the statements of the pinned OpenAI preprint *The crossing number of complete graphs* (openai/math at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`) as premises U1–U6, stipulated true and not re-proved. Every other step is proved in the paper. The new part is the lower bound for odd n >= 15. The upper bound, the even case and odd n <= 13 are classical consequences once the Harary–Hill formula is known; the paper says so and reproves them for completeness. Corollary B is new exactly for odd m >= 13.

Status: not accepted, not submitted, not uploaded. Independent manuscript review is pending. No machine-checked proof exists; see `formal-scope.json`.

## Reproduce

From this directory, with Python 3.9 or later (the recorded runs used 3.14.7):

```sh
python3 -B support/run_all.py
```

This runs, and fails (exit 1) if any of them fails:

1. a self-test that the output classifier rejects `SOME FAIL` with exit status 0;
2. SHA-256 authentication of the unchanged inherited checker copies in `support/inherited/`;
3. `support/release_checks.py`, the new checks R1–R9 (exact integers with integer division only, exact rationals, exact polynomial identities over Q), about 70 s;
4. the inherited author checker (about 2 min), compared line by line with its frozen output;
5. the inherited independent reviewer checker (about 25 s), compared byte for byte with its frozen output.

The result is `checks/run-receipt.json`. The optional mod-p subset needs NumPy:

```sh
python3 -B support/run_all.py --large-only --large-python /path/to/python-with-numpy --large-n 15 17 19
```

It wrote `checks/run-receipt-large.json` in about 20 minutes (NumPy 2.5.4). Orders 15, 17 and 19 are in the new odd range; the frozen log `support/inherited/author/kn_minus_e_modp_large.out` covers 13 <= n <= 19.

The finite checks support identities and bookkeeping used in the proof. They are not part of the proof and do not establish the theorem for any n beyond what they compute. They use different arithmetic: see Table 2 of the paper and `support/PROVENANCE.md`.

## Build

The paper uses standard LaTeX packages and an inline bibliography. With Tectonic and Poppler (`pdftoppm`, `pdftotext`, `pdfinfo`):

```sh
python3 -B support/build.py --tectonic /path/to/tectonic
```

This build used Tectonic 0.17.0 at `/tmp/frontier-typeset/tectonic` with `--only-cached` and `SOURCE_DATE_EPOCH=1792108800`. Two consecutive builds gave byte-identical PDFs. Other TeX versions may change bytes but not content. The script writes `checks/build/` (log, receipt, extracted text, pdfinfo) and renders every page to `checks/pages/`. It fails on overfull boxes, undefined references or rerun warnings. The manual page inspection is recorded in `checks/visual-review.json`.

## Package contents

- `main.tex`, `main.pdf`: the paper.
- `response-to-findings.md`: how each mandatory prior finding (1)–(7) is handled, with locations in the paper.
- `source-to-claim.md`: every external statement used, its exact locator, which claim depends on it, and what was read.
- `support/PROVENANCE.md`: origin, hashes, licenses and limits of every script, including the unchanged inherited copies.
- `input-manifest.json`: SHA-256 and byte sizes of every repository input read for this package, with read extents. Third-party reading copies are listed by hash only.
- `formal-scope.json`: formal verification pending; intended scope stated, unverified.
- `metadata.json`: authorship, licenses, scope and status.
- `RIGHTS.md`, `LICENSE-PROSE` (CC BY 4.0), `LICENSE-CODE` (MIT).
- `checks/`: run receipts, check outputs, build receipt and log, rendered pages, visual review.
- `public-files.json`, `public-manifest.json`, `kn-minus-edge-manuscript-public.zip`: the allowlisted public payload.
- `output-manifest.json`, `SHA256SUMS`: hashes of every file in this directory except those two (no circular hashes; `SHA256SUMS` also covers `output-manifest.json`).

`support/freeze.py` writes the public manifest, the deterministic ZIP, the output manifest and `SHA256SUMS`. `python3 -B support/verify_package.py` rechecks them, and `--with-inputs` also rechecks every input hash against the repository.

## Public boundary

The ZIP is built only from the allowlist in `public-files.json`. It contains the paper, original documentation, original code (MIT), the unchanged inherited scripts and their outputs (original MIT code by the same author), and check receipts. It contains no third-party paper, publisher PDF, web extraction, pinned upstream source copy, or internal review text. Those are referenced by link and hash only. `work/` holds local scratch (a text extraction of a third-party survey and an early trial receipt); it is excluded from the public payload and is not evidence for any claim. Nothing has been uploaded or published.
