# Edge-irregulator candidate manuscript and closed certificate

Candidate credit 0. Campaign 7/30 additional, 37/60 accepted; no acceptance edit.
Read paper.pdf (four pages, all personally visually inspected) and paper.tex.
Main endpoints: EdgeIrregulator.minimum_exact, fin_minimum_exact, main.
No t=1 optimum claim. Retained degrees are recomputed after deletion.

Reproduce in the existing pinned environment, with a nonexistent destination:

    sh build.sh /absolute/path/edge-irregulator-manuscript-packet.zip /absolute/path/fresh

The helper supervisor enforces AS512MiB, groupRSS512MiB, CPU210s/wall230s,
40ms nominal sampling, BLAS1. Each serial Lean compile has its own supervised
process group, AS infinity only in Lean, -j1 -M2700, RSS2800MiB,
CPU210s/wall230s, 45ms nominal sampling, warningAsError and autoImplicit=false.
The verifier checks the pinned binary, all nine packages and 1132 imported
package olean hashes; it starts with no own compiled artifacts and builds all
14 mathematical modules and both audits. Every actual type, origin, transitive
axiom closure and unsafe/partial/axiom flag is recorded for all 167 unique
actual declarations. Both audit logs must equal the saved logs byte for byte.
Paper and ZIP must rebuild byte identically. ZIP has no own prebuilt oleans.
The audit elaborators are outside the mathematical module set.

The PDF uses a pinned installed Tectonic executable and pinned existing cache,
copied into each extraction; --only-cached prevents network fetching. Four
small Computer Modern font assets are included. Their source is the public
MIT CTAN mirror, fonts/cm/ps-type1/bakoma/pfb/{cmr12,cmmi12,cmbx12,cmti12}.pfb.
No service/account writes or external posting occurred. This is environment-
pinned reproducibility, not a claim of a fully vendored TeX or Mathlib toolchain.

provenance.json identifies inputs, bytes and final-review obligations.
evidence retains ordinary proof, source/prior and root adoption pointers,
publisher PDF and inherited failures and supervision deviations. No worldwide
priority or new independent review is asserted. Root final review/current
refresh/acceptance remain separate gates. Sampling cannot exclude unsampled
resource transients or OS scheduling delays. No cap was raised.
