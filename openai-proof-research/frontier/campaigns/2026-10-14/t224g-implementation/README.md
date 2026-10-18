# T224G finite algebra implementation

Author: Myeongjin Kang, no affiliation. This is a scoped implementation for the immutable r103 candidate; it is not an independent review or a manuscript.

The copied pinned Lean4.34.1/mathlib setup compiles **8 supporting theorems plus8 definitions**, and **7 control theorems**. Every declaration's type and axiom dependencies were audited. Only propext, Classical.choice and Quot.sound occur; no sorry, admit, unsafe proof escape, native_decide, or conclusion-restating axiom is used.

**The geometric/percolation/process theorem is NOT formalized.** In particular this proves no arm estimate, screening, signed-measure transfer, Poisson generator identity, conditional-law convergence or J1 tightness. The replica product and telescoping identities here are scalar real algebra; no operator-valued or infinite product identity is asserted by Lean.

Run `python rebuild.py --output /var/tmp/NEW-T224G-BUILD` to copy sources to a fresh build directory, compile support and controls, and audit all declarations. Optional `--lean /path/to/lean --cache /path/to/packages` override machine paths. The runner verifies exact dependency commits and compiler version, does not use the network, and does not modify the shared dependency cache. Output must be a new directory outside this packet. The successful receipt/logs are under validation/.

See coverage.md for exact theorem/hypothesis mapping and provenance.md for copied infrastructure. Original code is MIT; original explanatory prose CC BY4.0, attribution Myeongjin Kang. No acceptance, publication or count change is claimed.
