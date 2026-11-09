# Round 2 validation

The source archive was safely extracted into the new empty verification/ directory.
All 13 modules compiled with warningAsError and passed leanchecker strictly serially.
The 3 inherited negative controls failed as intended. All 6 frozen sources match
both the original lane and the freshly extracted archive, before and after.

Audit2 covered 101 LOCAL declarations, including generated declarations, with zero
forbidden metadata flags. Their transitive axioms and the endpoint axioms are only
propext, Classical.choice and Quot.sound. The endpoint import closure contains
253037 declarations; its audited set equals its complete inventory in both directions.
Upstream metadata is separately reported in verification/replay-report.json.

This validates a partial conditional certificate, not an unconditional proof.
MainOrbit, FreeClassification and ExceptionalNoIso remain explicit premises.
No acceptance or discovery credit is claimed. Root decides.

Fresh resource summary: {"max_wall_s": 55.555, "max_peak_group_rss_kib": 3281876, "measured_invocations": 30, "background_jobs_left": false}
