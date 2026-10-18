# T212M conditional theorem — release implementation draft

This is a preparatory public selection, not an accepted result, final archive or publication. The theorem is conditional on the stipulated source at revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb: for every nonatomic Borel law on finite nonnegative iid square-lattice edge weights, almost surely no bigeodesic exists, simultaneously over all paths, without a moment assumption or fixed direction. Source212 already pays the finite min-of-four second-moment class; only its infinite-moment complement is additional. There is no unconditional conjecture-resolution or priority claim.

The original manuscript is unchanged. Manuscript r1 returned PASS_FULL_MANUSCRIPT_T212M with anchor c7942e070a2e01f03d27790f60d6225326f8f563a9364518f54a51cd3b9b3a99. Its parent adoption explicitly leaves coverage pending: AH6–7 and AH10 operative proof bodies were not read in that review. Focused r2 and actual parent closure remain pending in this draft. The policy has completion=null; final assembly refuses. A future review-closed package requires actual r2 evidence, externally supplied r2 and parent-closure hashes, and a newly externally anchored implementation policy. Neither a pass string nor an edited status substitutes for those bytes. Even review closure is not acceptance: accepted=false, published=false, count_change=0. Only the parent may adopt/count the result; uploads remain stopped.

Frozen records describing pending review or a 16-result campaign count are historical evidence of their writing time, not a current campaign ledger. Their bytes are retained without silently updating their status. The r1 adoption is likewise a historical incomplete adoption and cannot serve as final closure. Reading limits remain those of the individual author and reviewer reports. The supplied source identities, crosswalks and bounded-reading records do not establish that every primary work was read; omitted third-party source/primary bodies are not redistributed.

The draft allowlist contains 102 public evidence files, adding actual manuscript r1 evidence, its historical adoption, and the missing independent Lean reference log to the frozen preparation selection. Packet members are authenticated against their exact frozen manifests; parent records are individually bound. Manifests may name unselected private material for provenance, but this does not select it. No source/primary bodies, dependency caches, compiled Lean artifacts or write-in-place seal/review drivers are packaged.

## Identity and preparatory staging

Obtain the implementation manifest hash from the parent independently of this directory. All paths must be absolute, have no symbolic-link ancestor, and outputs must be new with existing parent directories. Use Python with -B to avoid adding bytecode caches to a verified selection.

```sh
python3 -B final_release.py preflight --implementation-anchor IMPLEMENTATION_SHA256 --campaign /absolute/campaign
python3 -B final_release.py stage --implementation-anchor IMPLEMENTATION_SHA256 --campaign /absolute/campaign --output /var/tmp/t212m-preparatory-stage
python3 -B final_release.py verify --implementation-anchor IMPLEMENTATION_SHA256 --manifest-anchor STAGE_MANIFEST_SHA256 --input /var/tmp/t212m-preparatory-stage
```

Staging prints its bundle-manifest hash. Retain this externally; verification requires both that anchor and the implementation anchor. Exact file and directory inventories are checked, including empty directories; symlinks, hardlinks and nonregular files are refused. The public allowlist and every helper are independently bound by the implementation manifest. Checks authenticate identity and scope boundaries; they do not establish mathematical correctness.

Future final assembly uses `assemble` with `--r2-anchor ACTUAL_R2_SHA256 --closure-anchor ACTUAL_PARENT_CLOSURE_SHA256`, the newly anchored implementation, campaign and new ZIP output. It is deliberately unavailable under the current policy. Final verification adds `--final` and the same external r2/closure anchors. ZIP members are sorted canonical POSIX names, with no directory entries, Unix regular-file 0644 permissions, timestamp 2026-10-18 00:00:00, empty comments/extra fields and DEFLATE level9. Byte determinism is within the same Python/zlib toolchain. The tool reads and validates ZIP members without extracting them. Use a trusted extractor only after verification, then verify the extracted tree again. No final ZIP is supplied by this draft.

## Separate standalone replays

Run these inside the authenticated extracted selection. Each command authenticates the entire selection before invoking the selected builder and checks it is unchanged afterward. Each output must be new and disjoint from source/tool/cache paths. For a final package also provide `--final --r2-anchor ... --closure-anchor ...`.

```sh
python3 -B replay_release.py pdf --implementation-anchor IMPLEMENTATION_SHA256 --manifest-anchor STAGE_MANIFEST_SHA256 --tectonic /absolute/path/tectonic --output /var/tmp/t212m-pdf
python3 -B replay_release.py original --implementation-anchor IMPLEMENTATION_SHA256 --manifest-anchor STAGE_MANIFEST_SHA256 --lean /absolute/path/lean --cache /absolute/path/packages --output /var/tmp/t212m-original
python3 -B replay_release.py independent --implementation-anchor IMPLEMENTATION_SHA256 --manifest-anchor STAGE_MANIFEST_SHA256 --lean /absolute/path/lean --cache /absolute/path/packages --output /var/tmp/t212m-independent
```

PDF uses cached TeX resources, fixed epoch and the original manuscript builder; it requires Tectonic, pdftotext and pdfinfo. Original Lean replay builds the two author modules and audits declared kernel dependencies. Independent replay separately runs the unchanged supplement driver: it builds those modules and the separately reviewed Independent.lean, checks exact compiler/dependency identities and compares the fresh full inventory log byte for byte with the reviewed reference. It does not repeat semantic mutation experiments. Compiler, TeX resources and cached Lean dependencies are trusted, not rebuilt. The supplement checks cache metadata before/after; this is not authentication of every cached artifact. The original builder has the narrower scanner/cache limits recorded in formal review O4.

Original formal v1 covers 14 support declarations and 17 controls. Its Fin4 examples instantiate finite segment lemmas, not infinite escape or tail theorems. The separately attributed reviewer supplement exposes 60 reviewer constants including infinite-graph nonvacuity, a metric-uniform threshold and hypothesis-deletion controls. Full stochastic FPP, coherent infinite rays, the cap construction, labels, Busemann limits and splicing are not formalized. Index-uniform tail cutoff requires external coercivity. The earlier supplement replay's printed 17 original/34 control/60 reviewer constants includes generated constants; it is not a new declaration count or full-theorem certificate.

Author Myeongjin Kang, no affiliation. Original prose CC BY4.0 and original code MIT; see the manuscript LICENSE.md. Review evidence preserves separate reviewer provenance. Third-party works retain their authorship and rights. This implementation adapts the checked T117Q/preparation identity helpers with T212M-specific selection and closure requirements.
