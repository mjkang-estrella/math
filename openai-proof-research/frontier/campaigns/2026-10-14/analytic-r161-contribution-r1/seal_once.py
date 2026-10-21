#!/usr/bin/env python3
"""One-time seal of this review's own selected packet; refuses existing envelopes."""
from pathlib import Path
import hashlib, json, runpy, sys
sys.dont_write_bytecode = True
r = Path(__file__).resolve().parent
for name in ['FINAL.md','MANIFEST.json','REPORT.md']:
    if (r/name).exists():
        raise SystemExit('Refusing reseal: '+name+' already exists')
v = runpy.run_path(str(r/'verify_packet.py'))
incoming = json.loads((r/'private/INCOMING-IDENTITY.json').read_text())
for entry in incoming:
    p = Path(entry['path'])
    b = p.read_bytes()
    if hashlib.sha256(b).hexdigest() != entry['sha256'] or len(b) != entry['bytes'] or oct(p.stat().st_mode & 0o777) != entry['mode']:
        raise SystemExit('Incoming original changed: '+entry['path'])
final = '''# Analytic161 contribution round 1

**TECHNICAL, conditional on correctness, for the full unchanged frozen statement.**

Scope SHA256: `53f35f024803059dd77264ffc0f00d0c20209a3768e61551e8285eccaf7d5b38`.
Author-proof SHA256: `22d6114f858c90872c502560f6b814766aab096f65cc16b081ee01d107577e2f`.

The complete reasoning is in [REVIEW.md](REVIEW.md). It derives the exact selection, filling/mass bounds, connectedness, dimension-only localization, finite-defect chord bound, barycenter estimate, every-point Psi and radius bounds for all n>=3 and all permitted delta, including zero. The core positive-deficit operation is the existing source integrating factor plus a globally signed quadratic Taylor bound, followed by optimizing (C-1)/a + gamma D^4 a. The source's asymptotic tangent coefficient then closes the estimate without a quantitative tangent scale or graph regularity theorem. The full compatible derivation, rather than theorem-title absence or a failed zero-start calculation, supports the contribution judgment.

Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb and its operative proofs are stipulated true. Wenger filling continuity, existing r58 threshold/chord assembly, BDF selection/localization/graph antecedents, and CAT(0) variance/density are credited. Euclidean graphical or Sobolev stability is not transported into arbitrary CAT(0). Q286's actual unrestricted asymmetry scope/calculations and all of T337E remain unchanged; this is not a replacement or resubmission of either.

[READING-AND-ISOLATION.md](READING-AND-ISOLATION.md) states exact actual extents and limits. Primary/source/history bodies and named metadata stay private/local under their original rights. No correctness review or peer/parent body was consulted. There is no correctness PASS, acceptance, count, or worldwide-priority claim. New deductions require separate correctness review. The seal and copied controls authenticate artifacts only.

This packet was sealed once with this file, MANIFEST.json and REPORT.md outside its selected payload. Their independent detached SHA256 anchors accompany the handoff. The verifier reads only and requires all three anchors.
'''
(r/'FINAL.md').write_text(final)
files, dirs = v['inventory'](r)
m = {'format':'analytic161-independent-selected-packet-v1','scope':'Entire immutable Analytic161 / T337A161 statement; contribution only, conditional on correctness','scope_sha256':'53f35f024803059dd77264ffc0f00d0c20209a3768e61551e8285eccaf7d5b38','outside_envelopes':sorted(v['ENVELOPES']),'directories':dirs,'files':[files[x] for x in sorted(files)]}
(r/'MANIFEST.json').write_text(json.dumps(m,indent=2)+'\n')
h = lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
report = f'''# Independent selected-packet report

Full-scope contribution verdict: TECHNICAL, conditional on correctness.

Payload: {len(files)} regular files, {len(dirs)} directories, with exactly three root-level outside envelopes. MANIFEST.json records this review's own membership, byte counts, SHA256s and modes; it is not an inherited author/source/history manifest. No symlinks or nonregular payload objects are accepted.

FINAL.md SHA256: `{h(r/'FINAL.md')}`.
MANIFEST.json SHA256: `{h(r/'MANIFEST.json')}`.
REPORT.md has its own independently computed detached hash in the handoff; no circular/self hash is attempted.

The supplied frozen statement/proof and three author envelope anchors were authenticated on intake. Immediately before this seal all twelve incoming direct author objects were rehashed and their modes compared with intake; no change was detected. Source selected members were independently matched to the complete pinned tree. Selected original r58/Q286 bodies and their membership were authenticated separately.

Seven private copied controls produced their expected outcomes: the synthetic baseline was verified; changed bytes, an extra file, a missing file, changed mode, changed envelope, and an extra empty directory were rejected. Their receipts are private/CONTROL-RESULTS.json. These are verifier-behavior checks, not mathematical evidence. The baseline used exact copied frozen/source bytes and a fresh control manifest; no author file was mutated.

This is a once-sealed contribution review with durable original mathematical reconstruction in REVIEW.md and detailed limitations in READING-AND-ISOLATION.md. Protected source/primary/history bodies, extracts, renders and named identities remain private. There were no shared edits, git/staging/commit, nested agents, browser UI, installations, publications/uploads/submissions/contacts or downstream work.

The author proof and this integrated reconstruction still require separate correctness review. No correctness PASS, acceptance, count, or worldwide-priority claim is assigned. Parent alone integrates and counts.
'''
(r/'REPORT.md').write_text(report)
anchors = {name:h(r/name) for name in sorted(v['ENVELOPES'])}
print(json.dumps({'anchors':anchors,'verification':v['verify'](r,anchors)},indent=2))
