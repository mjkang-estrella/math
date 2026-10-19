# Analytic/geometric discovery r115

Prefreeze research archive; no target or nominee. Start with research-report.md, then anisotropic-pressure-calculation.md. operation-comparison.md and reading-ledger.md bound the scope and provenance.

The packet separates original public prose/code from private retained source and primary bodies. Upstream pin: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Do not distribute private/ as original work.

The parent should obtain the detached manifest hash from ../FINAL.json or the handoff, independently of packet/manifest.json, and run:

    python -B packet/public/verify.py --packet packet --finalhash DETACHED_MANIFEST_SHA256

The verifier only reads. It requires the external hash, checks exact file/directory membership, modes, single-link regular files, lengths and SHA256. It does not execute diagnostics or judge mathematics. The verifier's own hash is separately in FINAL.json for bootstrap comparison. controls.py writes only disposable copies in the supplied owned control directory. checks.py performs small exact arithmetic diagnostics, not mathematical gates.
