# Retained failures and resource limits

attempt01 and attempt02 exceeded RSS2800MiB while loading broad Mathlib / tactic imports. Both were killed by the fixed Lean guard; no cap increase. attempt03 exposed deprecated-import warning, missing product Fintype, a cast issue and a recursive simp error. attempt04 compiled the generic real-linear bridge. attempt05 and finite01 exceeded RSS during one monolithic finite score computation. finite02 terminated at Lean's own -M2700 memory threshold. All guard JSON/log files are retained, including empty logs from killed loads.

The successful correction narrowed imports and split the 36 finite weight identities into separate kernel computations. finite03 then identified a rewrite affecting both sums; finite04 corrected it and passed. endpoint01 retained elementary vector simplification, cast, instance-name and real-number simplification failures; endpoint02 passed. endpoint03 retained a finite-image membership elaboration error; endpoint04 corrected it and passed. audit01 and the independent fresh extracted four-stage replay passed.

Some tool displays truncated long administrative/audit outputs. Full logs remain on disk and the guarded verifier parses the complete audit log; decisive source passages were read separately. Administrative JSON was parsed completely by the guarded preparation helper and accepted families inspected; no snapshot is represented as immutable campaign state.

The archived replay has no dependency on the staging scripts freeze.py, split.py, table.py, prepare.py or package.py; these scripts and their outputs remain for provenance. In particular, the staging scripts are not intended as idempotent replay entry points. Replay uses only the source-only archive's run.sh.

No network request was made. Existing preliminary-source access denials and novelty gaps remain unresolved; no denied GitHub/ScienceDirect/Google/Wiley route was retried and no historical HEAD loop was run.
