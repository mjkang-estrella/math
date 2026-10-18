# T118S author packet

Read report.md, original-scope.txt, candidate.md and reading-limits.md. Full unchanged author proof; TECHNICAL / NO NOMINEE. No independent PASS or count.

Verify with a caller-supplied external anchor:

    python -B verify.py --expected-manifest-sha256 ANCHOR

The verifier is read-only. It rejects extra/missing files or directories, changed payloads, symlinks, hardlinked files, other nonregular nodes and nested manifests. It checks source Git identities against the selected pinned tree entries and primary PDF/text identities. It does not establish mathematical correctness or novelty.

Original prose: Myeongjin Kang, no affiliation, CC BY4.0. Original code: MIT. Third-party bodies under private/ retain their original rights and are ignored; do not stage or publish them.
