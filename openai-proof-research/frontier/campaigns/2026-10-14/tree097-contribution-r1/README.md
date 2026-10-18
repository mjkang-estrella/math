TREE097 independent contribution/eligibility review, round 1. Verdict: TECHNICAL.

Read report.md (verdict, operation comparison, objections R1-R4/O1-O4),
then reading-limits.md and provenance.json. checkpoint.md summarizes.

Verify (read-only) with an anchor obtained from the external record, never
from this directory:

  python3 -B verify.py --expected-manifest-sha256 EXTERNAL_ANCHOR \
      [--author-root ../fresh-structural-discovery-r44]

verify.py checks the exact file AND directory inventory against MANIFEST.json
and the payload hashes. It rejects symlinks, hardlinks and other nonregular
nodes. Optionally it checks the four frozen author anchors. controls.py
reruns positive, wrong-anchor and mutation controls on /var/tmp copies only.
seal.py writes a manifest. Its output hash is meaningful only when recorded
externally. Integrity checks certify identity, not mathematics or novelty.

No third-party bodies are stored here; primaries are referenced by SHA256 in
the author packet's ignored private/ directory. Prose CC BY 4.0; code MIT.
