This source-only component proves `JacobiShifted.source_claim : JacobiShifted.SourceClaim`.
It contains 35 mathematical modules, comprising 30 unchanged frozen dependencies
and five new proof modules, plus three audit/interface modules.

Extract and rebuild into a NEW destination using the pinned local installation:

    python3 scripts/replay.py packet/source-claim-component.zip verification/a-new-empty-directory

The replay asserts the Lean executable SHA and mathlib revision, checks the
archive's manifest before and after, rejects local prebuilt artifacts, and
builds sequentially with the unchanged `run_lean.py` under the sampled process-tree
3 GiB RSS guard. It sets -j1, -M4096, warningAsError=true, autoImplicit=false,
and a 512 MiB diagnostic file cap without an address-space cap. It checks that
all mathematical logs are empty and matches the exhaustive origin/safety
inventory with actual #check/#print axioms output for every new declaration.
Only propext, Classical.choice and Quot.sound are permitted.

The two audit elaborators enumerate or inspect declarations; they supply no
mathematical facts. The exact literal definitions are in unchanged SourceDefs.lean.
No manuscript, novelty clearance, independent final review, acceptance or count
change is represented by this component.
