#!/usr/bin/env python3
"""Author-side sealing: write packet/MANIFEST.json and FINAL.json (REPORT.md must already exist)."""
import hashlib, json, os, stat
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / 'packet'
ROUND = 'fresh-arithmetic-discovery-r99'
STATUS = 'AUTHOR_PROOF_NOMINEE'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    files, dirs = {}, {}
    for base, ds, fs in os.walk(PACKET, followlinks=False):
        bp = Path(base)
        dirs[bp.relative_to(PACKET).as_posix()] = stat.S_IMODE(bp.lstat().st_mode)
        for f in fs:
            p = bp / f
            r = p.relative_to(PACKET).as_posix()
            if r == 'MANIFEST.json':
                continue
            s = p.lstat()
            files[r] = {'bytes': s.st_size, 'mode': stat.S_IMODE(s.st_mode), 'sha256': sha(p)}
    manifest = {'round': ROUND, 'status': STATUS, 'directories': dirs, 'files': files}
    (PACKET / 'MANIFEST.json').write_text(json.dumps(manifest, indent=1, sort_keys=True) + '\n')
    final = {
        'schema': 'r99-detached-anchor-v1',
        'round': ROUND,
        'status': STATUS,
        'family': '164',
        'nominee': 'Theorem F (FS/FP partition regularity in every infinite field) with Corollary G (F_{p^m}, d | m)',
        'frozen_target': 'packet/public/scope-freeze.md',
        'scope_freeze_sha256': sha(ROOT / 'freeze/scope-freeze.md'),
        'frozen_utc': '2026-10-20T17:20:23Z',
        'self_gates': None,
        'count': None,
        'runner': 'Factory Droid / claude-opus-5-5 / high',
        'pin': 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',
        'tree_sha256': sha(ROOT.parents[3] / 'sources/preprints-tree.json'),
        'manifest_sha256': sha(PACKET / 'MANIFEST.json'),
        'verifier_sha256': sha(PACKET / 'code/verify.py'),
        'controls_sha256': sha(PACKET / 'code/controls.py'),
        'public_report_sha256': sha(PACKET / 'public/report.md'),
        'proof_sha256': sha(PACKET / 'public/proof.md'),
        'report_sha256': sha(ROOT / 'REPORT.md'),
    }
    (ROOT / 'FINAL.json').write_text(json.dumps(final, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'final_sha256': sha(ROOT / 'FINAL.json'), 'manifest_sha256': final['manifest_sha256'],
                      'report_sha256': final['report_sha256'], 'files': len(files), 'dirs': len(dirs)}))


if __name__ == '__main__':
    main()
