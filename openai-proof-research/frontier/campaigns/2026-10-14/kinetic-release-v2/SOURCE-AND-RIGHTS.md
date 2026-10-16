# Sources, restoration and rights

The stipulated source truth pin is OpenAI/math commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. This package does not independently audit that upstream truth. `../kinetic-manuscript-consolidation/source-H.json` records ten exact upstream paths, pinned raw URLs, SHA256, Git blob SHA1, byte lengths and read extents. The corrected source map, source-sections file, references, exact TeX diff and response explain dependencies and N1–N7. Earlier continuity/centering notes are retained with their provenance. Historical contribution-review sources record the bounded external-literature screen actually performed; no new literature search is claimed.

No raw H files or external literature PDFs/extracts are selected. In a disposable manuscript copy, optional source retrieval is:

```sh
python3 verify_sources.py --fetch --project-root /nonexistent
```

This uses exact pinned URLs, checks size/SHA256/Git blob SHA1 and deletes its temporary downloads. It was not rerun by this preparation and is not needed by the standalone bundle verifier. The verifier may leave an empty `tmp/` within that disposable manuscript copy.

For the full corrected historical `verify.py`, restore all **30 excluded records** from its 107-record input manifest: ten raw H sources, the original upstream tree snapshot and nineteen original-edition page PNGs. **77** corrected historical input records are selected. The original 54-record manuscript manifest has **11** omitted inputs; the original review's 50-record authentication has **10** omitted raw H sources. All exact paths, sizes and hashes are in `excluded-inputs.json`; manifests themselves are unchanged. Restore into a disposable extracted root, not the authenticated publication tree. Run historical scripts only on copies because they rewrite receipts; use Poppler for PDF inspection. Source fetch alone does not restore the tree index or original page images.

The original `sources/preprints-tree.json` is an authenticated historical GitHub API snapshot; regenerating an equivalent tree is not guaranteed to reproduce its JSON bytes. Obtain the matching frozen snapshot. The omitted original PNGs can be obtained from the frozen original manuscript tree and checked against the recorded hashes. The original PDF is retained, but a fresh renderer/version may produce different PNG bytes.

Formal `.olean`/`.ilean` files, dependency caches, local build directories, third-party raw documents and unrelated projects are excluded. The formal review manifest's old `fresh/KineticSupport.olean` reference is retained as historical evidence only; its bytes are not included. Restore it only for a historical byte check if available, or use `rebuild_lean.py` for fresh scoped support compilation. Dependency binaries themselves are neither redistributed nor independently rebuilt here.

The two manuscript PDFs are intentional: the corrected primary paper and the original document to which review-r1 binds. Only the corrected edition's nineteen page renders are selected. Small duplicate source/control files are retained when needed to understand exact historical dependencies or run the portable checks. The old release machinery is authenticated as preparation input; the new package does not include a second complete old release.

Author: Myeongjin Kang, no affiliation. Original prose/paper CC BY 4.0; original code/Lean MIT. The selected manuscript and formal license files govern author material. Copied code keeps its notices. Upstream sources, external literature, Lean, mathlib and other dependencies retain their own rights and licenses. No author license purports to relicense third-party materials.
