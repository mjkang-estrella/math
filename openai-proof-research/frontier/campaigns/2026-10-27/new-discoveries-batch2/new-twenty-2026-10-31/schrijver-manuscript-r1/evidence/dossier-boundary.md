## 8. Reproducibility and dossier boundary

The editable manuscript is paper.md; scripts/render.py produces paper.pdf. Supplied font files make rendering reproducible with ReportLab. Every PDF page is rasterized and visually inspected, with page hashes and findings recorded in qa/receipt.json. The PDF is a draft artifact, not an acceptance decision.

The proof packet is schrijver-source-r5.zip. Its byte hash is stated in §5 and in the delivery manifest. The safe-extraction test rejects absolute paths, parent traversal, links, duplicate members, and compiled-object suffixes, checks source-manifest entries, and counts 474 source modules. Extraction is into proof-packet-safe inside this lane. No archived replay script is executed here.

PROOF.md states the mathematical argument and its exact formal scope. REPRODUCE.md distinguishes commands for the ordinary certificate check and manuscript rendering from the future formal replay reserved to root. The exact MathDB raw line is mathdb-352827.raw.jsonl, with SHA-256

b5f22645d8c39a7b9b81ebb016b3fa3bbc79b47330eea97cfb10693e12468a15.

The dossier contains source copies, access receipts, historical formal summaries, the r5 reports, both reviews, complete ordinary graph certificates, retained search records, and the parent's registry-refresh receipt. It also includes the script and results of this lane's fresh ordinary checks of SG(14,6), SG(27,12), SG(28,12), SG(29,13), and SG(30,13). Those checks independently regenerate stable masks, compare every literal adjacency, verify exact BFS layers, and exhaust rotation coverage.

Input manifests bind read-only upstream files and rendering dependencies before artifact production and again at completion. A procedural exception is retained in the operational receipt: initial brief, policy, inventory, and report reads preceded the capped/hash-bound artifact workflow. We do not claim these initial reads were pre-bound. Subsequent inputs were frozen for copying, checking, and authorship, and completion hashes test that they remained unchanged. No other lane was modified.

All numerical and rendering work in this lane is serial, restricted to two CPUs, CPU 120 seconds and wall 140 seconds per command, with MALLOC_ARENA_MAX=2 and a 6 GiB address-space ceiling; sampled process memory is recorded for the render and raster steps. The initial uncapped lightweight reads are disclosed rather than silently represented as compliant.

The full-dossier ZIP includes the unchanged proof packet and all listed delivery evidence. Its manifest excludes itself and the outer ZIP to avoid circular hashing. A separate delivery hash file binds the final PDF, source, manifests, and both ZIPs. Temporary rendering dependencies are omitted from the ZIP; the renderer also works with an installed ReportLab distribution.

**Status at handback.** The draft refutes the arXiv v2 unit-gap statement using the r=3 instance. The supplied formal packet has no residual mathematical hypotheses, according to its source and independent fidelity review. Root's decisive replay is pending at this snapshot; journal-body access and worldwide novelty remain qualified. No publication, priority claim, self-acceptance, or separate correction credit is made. Root alone decides acceptance.
