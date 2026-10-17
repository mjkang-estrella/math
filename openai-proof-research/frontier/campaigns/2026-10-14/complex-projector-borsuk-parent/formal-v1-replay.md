# B8C formal implementation: parent replay

The implementation is received, not yet independently accepted at the formal gate. Full B8C scope and the prior proof/contribution decisions are unchanged; count remains 6/10.

The externally supplied output-manifest anchor is `28429901ed26db71aaa1bc3b4b7c62c1f2c38f945510e04ba4e4f48eb5893700`; core source is `8c6863344596404bf7f8e13e341972510f3ad7d4fa63308a9d31872a9d947cab`. Parent read the complete core, controls, both query files, coverage, verifier, rebuild/mutation/checked-run/semantic-check scripts, provenance and input manifest. Candidate Lemma11 through CorollaryC was read against the exact types.

Externally anchored verification passed 57 sealed payloads and all six fixed external records; a wrong anchor was rejected. Parent ran `rebuild.py --output .replays/parent-formal-r1` and `mutations.py --output .replays/parent-mutations-r1`. Fresh compilation passed 16 support theorems, 19 public declarations and 13 controls. All exact type/axiom and arithmetic-control output equals the sealed clean build byte-for-byte. Five false variants failed at mathematical proof goals. All nine pinned dependency tracked trees are clean. Standard propext/Classical.choice/Quot.sound dependencies only; existing pinned dependency objects remain trusted and were not rebuilt.

The content proves the exhaustive scalar two-trio margin and exact complex expansion with the conjugate in the right position. `local_score_improves` takes the F/O estimates as hypotheses; it does not establish actual trio selection or geometric scores. Compactness, the complement gap, all CP2/PSD/Borsuk-Ulam topology, and Bessel/attained diameters remain outside Lean. These boundaries agree with coverage.json. This is useful supporting formalization, never a full B8C formal certificate.

A separate reviewer now audits the sealed package in `complex-projector-borsuk-formal-review-r1`. Parent replay logs are retained in the documented unsealed replay directory, and the manifest remains unchanged. No frozen bytes were edited. Original prose CC BY4.0; Myeongjin Kang, no affiliation.
