# Final extracted replay

Status: PASS for the partial packet; NOT acceptance of the conjecture.

The final source.zip SHA256 is a3d3b2d14c760fb95f64c2eb103a5358740ff403a6aa264e2b58ed8ee3df7e80. Its paths were listed and its archive integrity checked with unzip. It was extracted into a newly empty lane-local replay/ directory. All seventeen modules compiled strictly and all seventeen explicit-module leanchecker calls returned zero. The final script completed with exit zero. Exact stdout/stderr logs are retained in replay/logs/ with unique names; successful module markers are in replay/build/.

The final audit covers 9,610 declarations: 295 local and 9,315 upstream. Every dependency is in the audited set. Local unsafe, partial, unsafe-rec, implemented_by and extern counts are zero. Upstream metadata separately includes 109 partial/unsafe-rec declarations, five implemented_by and 51 extern declarations. The only axioms are propext, Classical.choice and Quot.sound. This is not a blanket absence claim about upstream execution metadata.

The 42-case independent Python checker and its three negative controls passed. All six finite literal-graph certificates and the inherited row checks passed kernel checking. All seven frozen source hashes passed both in the lane and in the extraction.

The preceding replay-initial/ directory records an earlier partial packet before the finite regression bridge was added. It is preserved as development evidence and is not the final replay. No background job is retained at handback.
