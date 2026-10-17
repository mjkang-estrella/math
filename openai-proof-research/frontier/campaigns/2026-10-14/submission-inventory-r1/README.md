# Authenticated submission queue: R023–R027

The five accepted results have ready local PDF/ZIP pairs and prepared metadata. No upload, account change, public submission, or private credential access was performed by this task. Public submission was authorized by the user's latest instruction; the parent owns authenticated sessions and actual publication. S2/R028 is outside this inventory.

Use `submission-inventory.json` for exact absolute paths, SHA-256, byte lengths, full accepted statements, source assumptions, gate evidence, formal limits, exact TeX abstracts, and readable abstracts. Use `r023-zenodo-metadata.json` through `r027-zenodo-metadata.json`, and corresponding MathDB files, as ready metadata. They are templates, not executed API payloads. MathDB's `abstract_plain_text` avoids local TeX macros that its editor may not define. Exact abstract TeX is retained for provenance.

| Result | Final paper directory | PDF pages | Final release ZIP |
|---|---|---:|---|
| R023 | `p-gradient-publication-v1/output/pdf/main.pdf` | 20 | `r023-p-gradient-publication-v1.zip` |
| R024 | `matrix-disk-manuscript/output/pdf/main.pdf` | 11 | `r024-matrix-disk-v2.zip` |
| R025 | `kinetic-manuscript-consolidation/output/pdf/main.pdf` | 19 | `r025-functional-hard-sphere-fluctuations-v1.zip` |
| R026 | `staircase-manuscript/main.pdf` | 6 | `r026-integral-staircase-regular-summand-v1.zip` |
| R027 | `kn-minus-edge-manuscript-r2/main.pdf` | 15 | `r027-complete-graph-minus-edge-v1.zip` |

Paper paths above are relative to `openai-proof-research/frontier/campaigns/2026-10-14/`; ZIPs are in `openai-proof-research/output/release/`. R023's historical 21-page proof PDF and old ZIP are not the publication selection. R024's v1 ZIP omits the later scoped formal support. Do not silently replace the selected reviewed papers with a rebuild.

All five selected ZIP digests match their final receipts. Every manifest-listed payload hash and byte count was recomputed, all ZIP CRCs pass, all standalone PDFs and TeX equal the corresponding archived bytes, and all listed proof/contribution/manuscript/scoped-formal review artifacts equal the archived copies. R023 and R024 additionally contain a `BUNDLE-README.txt` outside the project-file manifests; its bytes are authenticated by each full archive digest. The other three archives have exact manifest membership plus the manifest. These checks authenticate artifacts, not a new proof audit. The accepted finding records and actual independent gate decisions were read; existing complete review conclusions are not renamed external peer review.

Each upload identifies Myeongjin Kang, with no affiliation. Paper/original prose: CC BY 4.0. Original code/Lean: MIT. Preserve third-party rights. Descriptions disclose AI-assisted authorship/review, internal independent agent review rather than external peer review, stipulated pinned OpenAI inputs, bounded literature comparison, and the exact partial formalization boundary. None of these papers has a full Lean proof.

## Destination requirements and routing

Zenodo's official [upload guide](https://help.zenodo.org/docs/deposit/create-new-upload/) supports mixed resource uploads and requires basic metadata; use publication/preprint for these paper-plus-support packages. Set the publication date to the actual first public release date, not the paper's preparation date. No DOI is assumed; let the real deposit reserve/register it. Save and preview the actual form to validate its required fields. The current [license guide](https://help.zenodo.org/docs/deposit/describe-records/licenses/) explicitly permits mixed licenses: declare both CC BY 4.0 for prose and MIT for original code, with their scopes. Core JSON uses legacy deposition names only as a convenient metadata template; current GUI fields govern.

MathDB provides a stand-alone [paper upload route](https://mathdb.com/papers/new); read-only access currently says sign-in is required. No exact open-problem match is required to prepare a paper record. R023 must not be submitted as a full solution of [405360](https://mathdb.com/p/405360/the-c-p-regularity-conjecture), whose inhomogeneous/all-p/sharp-exponent scope is broader. R024 must not be submitted as a fresh proof of [392465](https://mathdb.com/p/392465/complete-crouzeix-conjecture), which is the credited inequality input. No exact integral/every-ring, kinetic-path-space, or missing-edge problem route was authenticated here. Use independent paper records, with accurately scoped related-result links if the actual workflow permits.

## Duplicate checks and remaining prerequisites

The official Zenodo public API author query returned 12 records and five exact-title queries returned zero records, all with HTTP 200. Those 12 titles are earlier findings, not these five. See `zenodo-author-lookup.json` and `zenodo-exact-title-lookup.json`. Public indexing cannot establish absence of private drafts, alternate titles, or freshly unindexed records. Parent should inspect the authenticated user's drafts/uploads before creating new deposits.

The current MathDB paper listing exposes eight Kang papers, none matching these five titles or abstract scopes. The closest two, [2610.00018](https://mathdb.com/abs/2610.00018) and [2610.00019](https://mathdb.com/abs/2610.00019), were read individually. They concern dimension-four scalarization and a dimension-six obstruction to coefficient compression. They are antecedents to R024, not duplicate publication of its all-dimensional disk-rigidity theorem. See `duplicate-checks.json` for the comparison and bounded read extent.

No local artifact blocker was found. Remaining practical prerequisites are an authenticated parent session and checking its private drafts before creating public records. Final DOI/record URLs must come from actual service responses. These are access/duplicate checks, not a request for renewed publication permission.

Reproduce local authentication, then regenerate metadata in this directory:

```sh
python3 build_inventory.py
python3 prepare_metadata.py
```

These scripts do not upload or touch frozen packages. Their only writes are inventory/metadata in this assigned directory. Original prose CC BY 4.0; original scripts MIT.
