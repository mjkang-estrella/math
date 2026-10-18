# T205M manuscript version 1

Myeongjin Kang, no affiliation. Author-prepared manuscript for independent review; no manuscript acceptance or campaign count is asserted. Original prose CC BY 4.0; original code MIT.

The complete article is `public/article.tex`; the 13-page rendered manuscript is `output/pdf/article.pdf`. The unchanged theorem covers every m≥2 and every nonrow, noncolumn partition of m(m+1)/2, with sharp lower bound m−1. Both uniform combinatorial proofs are included in full. The exact finite starts are disclosed and reproducible from the original public code and certificate.

`editorial-response.md` addresses proof E1–E6, mandatory contribution C1/C2, and the exact limits of the subsequent scoped formal review. In particular, Section5.1 supplies a newly read actual KSS primary statement for the unbounded rigged-configuration convention. I19's recursion/max rule, I21's Kostka refinement, Kirillov's operations and parent high-capacity assistance are credited explicitly. No new-to-literature priority is claimed.

`input-anchors.json` and byte copies under `provenance/` pin the immutable author, proof, contribution, scoped formal and formal-review records. `source-identities.json` independently matches21 source blobs against the complete canonical tree. `primary-receipts.json` identifies five private PDF/text pairs. `reading-limits.md` distinguishes semantic reads from retrieval and identity checks. Original packets were not edited.

`development/build05/` holds the final deterministic cached build; `development/copied-build-final/` is an identical-PDF rebuild from a copied public directory. `inspection/page-inspection.json` and individual PNGs record every page's visual check. Earlier failed font-cache builds and intermediate renders are retained as development chronology, not final failures. Final builds have no layout/reference warnings. The finite proof replay and degree-ten character crosscheck pass; their precise limits are stated in the article.

Only `public/` and the final PDF are intended manuscript deliverables. Private third-party bodies are ignored and must not be staged or released. No release, staging, commit or upload was performed. The public source inventory gives exact bytes; the parent handles any later independent manuscript review and release.

## Authentication

Obtain the manifest anchor from the external parent handoff, then run:

```sh
python3 -B verify.py --anchor EXTERNAL_SHA256
python3 -B integrity-controls.py --anchor EXTERNAL_SHA256
```

The verifier is read-only and self-contained. It requires the caller's anchor, rejects extra or missing files/directories, all symlinks including ancestry, hardlinks, nonregular entries, and nested manifests. It authenticates source, primary, provenance, build, PDF and page identities. It does not independently prove mathematics or confer a review verdict. Controls mutate disposable copies under `/var/tmp`; they do not alter the sealed original. Any retained preseal control receipt is labelled as such; the final controls are rerun against the final externally reported anchor.

The scoped Lean support contains 17 named declarations (2 definitions and15 theorems) about finite-poset rank interpolation, unique-rank cuts and two-ideal reduction. The independent review also audited generated constants. The skew geometric no-cut condition and all representation theory, configuration enumeration, finite bases and full induction remain unformalized. This task did not rerun Lean or rebuild its trusted cache.
