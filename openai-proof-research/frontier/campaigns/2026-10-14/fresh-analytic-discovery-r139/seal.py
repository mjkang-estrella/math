"""One-shot local envelope writer. Never rerun to refresh a sealed packet."""
from pathlib import Path
import datetime
import hashlib
import json
import sys

sys.dont_write_bytecode = True
from verify import ENVELOPES, inventory


def write_new(path, text):
    with path.open('x', encoding='utf-8', newline='\n') as stream:
        stream.write(text)
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    root = Path(__file__).resolve().parent
    if any((root / name).exists() for name in ENVELOPES):
        raise SystemExit('Refusing: an original envelope already exists.')
    manifest = {
        'schema': 'r139-exact-payload-v1',
        'sealed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'status': 'PREFREEZE / no nominee',
        'excluded_root_envelopes': sorted(ENVELOPES),
        'inventory': inventory(root),
    }
    manifest_hash = write_new(root / 'MANIFEST.json', json.dumps(manifest, indent=2) + '\n')
    report = f'''# Analytic discovery r139 — parent handoff

PREFREEZE / no nominee. No theorem was frozen. No correctness, contribution,
acceptance or count is assigned; parent alone integrates and reviews.

The sustained family was Source374 Brenier transport stability. The explicit
fixed-target optimality identity G0+G1 <= wD, combined with the primary
fourth-power conditioning proof D^4 <= A G0, gives D <= C w^(1/3).
Known same-subgradient oscillation supplies the common-coordinate comparison,
and the pinned source pays uniform-reference target changes. These compatible
operations account for the proposed cube-root extension. DERIVATION.md gives
the hypotheses, calculations and source interfaces.

The unpaid operation is an improved coupling of optimal graph plans for fixed
target and varying source, uniform over target masses and cell geometry.
The current upper exponent is 1/3; the explicit localized example excludes
exponents above 2/3. A square-root upper estimate would need squared product
cost O(w), which is not proved. Sharpness for a fixed source-optimal lift or for
common-coordinate maps does not establish sharpness of the optimized graph
metric. GAPS.md records this precise distinction. No worldwide-priority or
current-open claim is made, and no old full scope is reoffered.

Provenance: Codex / GPT-6 Astra / high / default service tier. Pin
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb and operative proofs were stipulated,
without truth audit. Nine selected pinned source bodies are authenticated
against the complete 13,223-entry tree. Five exact primary source versions
were acquired, with actual partial and unread extents explicitly recorded.
Source, primary and history identity ledgers are payload; private bodies retain
their original rights. Selected-copy membership is separate from selected
current-original observations and is not original-root authentication.

READING-LIMITS.md and ISOLATION.md disclose false catalogue/history/body
admissions, late original reads, coarse omissions and truncated displays.
The same-turn arithmetic r111 addition was recorded before further selection,
after copied integrity controls and before sealing; no broad scan followed.
Earlier scan records preserve their actual filters. This is not a retrospective
isolation, exhaustive history, OS preservation or family-budget certificate.

All intentional outputs remain in the exclusive root. There was no nested
agent, git/staging/commit, publication, upload, contact, browser UI or downstream
formal/manuscript/release work. Named completed originals were not modified.

Six small copied integrity cases checked clean/restored membership, changed,
missing and extra payloads, and a wrong external anchor. They use a separate
synthetic manifest. Artifact controls are not mathematical gates.

The exact original payload manifest SHA256 is:
{manifest_hash}

MANIFEST.json, REPORT.md and FINAL.md are the three envelopes outside the
manifested payload, still inside the authorized root. Independent detached
hashes must be supplied to verify.py; it only reads and never repairs or reseals.
'''
    report_hash = write_new(root / 'REPORT.md', report)
    final = f'''# FINAL — analytic discovery r139

PREFREEZE / no nominee. No frozen statement, author-proof nominee, self-gate or
count. See DERIVATION.md, GAPS.md and REPORT.md for the complete handoff.

Strongest integrated reduction: fixed-target two-gap optimality plus known
fourth-power conditioning gives cube-root source stability; known oscillation
and pinned Source374 complete the corresponding routine comparisons.

Unresolved: a uniformly improved coupling of graph plans. The derived upper
exponent is 1/3, and the example only obstructs exponents above 2/3. No stronger
full result closes. This is no new conjectural finding or current-open claim.

Read limits, false admissions and the prospective same-turn r111 exclusion
are recorded in READING-LIMITS.md, ISOLATION.md and ISOLATION-STEER.json.
Source/primary/history bodies remain private under their original rights.
Parent alone performs integration, independent reviews and any count.

Detached MANIFEST.json SHA256:
{manifest_hash}

Detached REPORT.md SHA256:
{report_hash}

FINAL.md's own independent SHA256 is supplied outside these envelopes.
Run verify.py with all three explicit detached anchors. Verification concerns
exact bytes and membership only; it supplies no mathematical verdict.
'''
    final_hash = write_new(root / 'FINAL.md', final)
    print(json.dumps({'MANIFEST.json': manifest_hash, 'REPORT.md': report_hash,
                      'FINAL.md': final_hash}, indent=2))


if __name__ == '__main__':
    main()
