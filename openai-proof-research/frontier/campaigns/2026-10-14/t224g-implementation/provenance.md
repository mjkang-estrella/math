# Provenance and build limits

The original local algebra was written for the current T224G support task. binding.json anchors the immutable r103 candidate and exact relevant notes. No r103 byte was edited.

rebuild.py was adapted from t212m-formal-v1/rebuild.py (SHA256 065081793ead8972e93ada22d8fe7aed2bb7a34d88104c7e0d3e2c18ffa5e404) after reading it in full; changes replace the support module/namespace names. lean-toolchain and dependency revisions were copied from that frozen infrastructure. lake-manifest.json's PROJECT NAME was corrected from the inherited historical name to t224g_scoped_support; dependency entries are unchanged. The successful compile used those exact dependency commits; the project name is not read by the direct compiler runner.

Lean:4.34.1, compiler commit5045d0056413266e57c625dcd7c365b10e377c52. Mathlib:d13f23b723b8a846827a245b89c10fc7d3f11612. Compiler binary hash, all package commits, source hashes and individual axiom reports are in validation/receipt.json. Sources were copied before execution; shared caches were checked for tracked modifications and were not changed. No third-party source script was executed.

Two development attempts exposed ordinary Lean issues (real division requires noncomputable definitions, an unnecessary tactic, and closing the unnamed section). These were corrected before the successful warning-free support/control/audit run in /var/tmp/t224g-lean-final-build. The retained validation logs are that successful run, not substituted outputs from earlier attempts.

No formal independent review, contribution verdict, manuscript, acceptance or publication is claimed. This implementation does not read pending reviewers or alter the mathematical candidate.
