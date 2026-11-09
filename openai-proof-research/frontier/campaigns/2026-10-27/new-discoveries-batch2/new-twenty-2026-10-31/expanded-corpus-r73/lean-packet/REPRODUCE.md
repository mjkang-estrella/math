# Reproducing the MathDB 378395 packet

1. Extract `source-only-packet.zip` into a NEW empty directory. It contains no .olean files.
2. Run from the extraction root:

       LEAN_BIN=/path/to/lean-4.34.1-linux/bin \
       LEAN_PACKAGES=/path/to/formal/.lake/packages \
       python3 -I replay.py

   The pinned Lean 4.34.1 binary and leanchecker hashes are in `pins.json`. The packages directory must hold the prebuilt mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 oleans, which are treated read-only.
3. The driver checks binary and source hashes and refuses pre-existing outputs. It then builds `proof/MathDB378395.lean` with `-j1 -DwarningAsError=true` (the log must be empty), runs `leanchecker MathDB378395`, and runs the full local-declaration audit (134 constants, transitive axioms ⊆ {propext, Classical.choice, Quot.sound}, no sorry/unsafe/partial/extern/implemented_by/axiom/opaque). Next come the sanity supplement, one positive harness control, five negative controls (perturbed certificate, wrong endpoint, sorry, forbidden axiom, malformed olean), and the exact Python diagnostic. Every call is capped at 2 CPUs, CPU 120 s, wall 140 s, AS 64 GiB and a 6 GiB guard on the sampled private RSS.

Trust limits: the prebuilt dependency oleans are trusted. There is no full upstream rebuild and no source-to-olean attestation. Sampled RSS is not cgroup enforcement unless the systemd scope is available.
