Independent full-scope proof review of TREE097 (round 1).
Verdict: PASS_FULL_TREE097 (proof gate only; not contribution/eligibility).

Read report.md first, then rederivation.md, reading-and-limits.md,
provenance.json and checkpoint.md. checks/ holds a supplementary finite
diagnostic (not proof evidence) and the integrity-control script and result.

Verify with
  python3 -B verify.py --expected-manifest-sha256 CALLER_SUPPLIED_EXTERNAL_ANCHOR
The anchor must come from the reviewer's handoff, not from any file here.
The verifier is read-only, checks the exact file AND directory inventory,
and rejects symlinks, hardlinks, nested manifests and nonregular nodes.
No third-party bodies are stored here. Prose CC BY 4.0; code MIT.
