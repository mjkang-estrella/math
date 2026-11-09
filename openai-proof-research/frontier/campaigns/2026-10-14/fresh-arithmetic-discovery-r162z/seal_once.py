#!/usr/bin/env python3
"""One fresh r162z seal. No inherited or reduced-selection manifests."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

PROJECT = Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
ROOT = PROJECT / 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162z'


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def make_manifest(root, selected_roots, extras):
    paths = set(extras)
    for name in selected_roots:
        for p in (root / name).rglob('*'):
            if p.is_symlink():
                raise RuntimeError('symlinks are not permitted')
            if p.is_file():
                paths.add(p.relative_to(root).as_posix())
    return {'version': 1, 'selected_roots': selected_roots,
            'extra_files': extras,
            'selection_note': 'Fresh exact own selection; no inherited manifest.',
            'files': [{'path': name, 'bytes': (root/name).stat().st_size,
                       'sha256': digest(root/name)} for name in sorted(paths)]}


def write_json(p, value):
    p.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')


def anchors(root):
    return {name: digest(root/name) for name in ('FINAL.md', 'MANIFEST.json', 'REPORT.md')}


def run_verify(root, anchor):
    return subprocess.run([sys.executable, str(ROOT/'verify_packet.py'),
                           '--root', str(root),
                           '--final-sha256', anchor['FINAL.md'],
                           '--manifest-sha256', anchor['MANIFEST.json'],
                           '--report-sha256', anchor['REPORT.md']],
                          cwd=PROJECT, capture_output=True, text=True, timeout=30)


def main():
    if Path.cwd() != PROJECT:
        raise RuntimeError('required command workdir mismatch')
    for name in ('MANIFEST.json', 'REPORT.md', 'ANCHORS.json', 'controls'):
        if (ROOT/name).exists():
            raise RuntimeError('refusing to repeat or overwrite a seal/control run')
    control = ROOT/'controls/copied-own-text'
    (control/'packet').mkdir(parents=True)
    shutil.copyfile(ROOT/'FINAL.md', control/'FINAL.md')
    fixture = control/'packet/own-text-control.txt'
    shutil.copyfile(ROOT/'packet/own-text-control.txt', fixture)
    (control/'REPORT.md').write_text('Tiny copied own-text control, not a mathematical gate.\n')
    write_json(control/'MANIFEST.json', make_manifest(control, ['packet'], ['FINAL.md']))
    ca = anchors(control)
    results = []
    baseline = run_verify(control, ca)
    if baseline.returncode:
        raise RuntimeError('baseline control failed: '+baseline.stderr)
    results.append({'control': 'fresh tiny copied selection', 'expected': 'PASS',
                    'returncode': baseline.returncode, 'output': baseline.stdout.strip()})
    saved = fixture.read_bytes()
    fixture.write_bytes(saved+b'tamper\n')
    altered = run_verify(control, ca)
    fixture.write_bytes(saved)
    if altered.returncode == 0 or 'payload mismatch' not in altered.stderr:
        raise RuntimeError('tamper control failed to detect changed copied bytes')
    results.append({'control': 'copied-byte tamper', 'expected': 'REJECT',
                    'returncode': altered.returncode, 'output': altered.stderr.strip()})
    extra = control/'packet/unlisted-own-text.txt'
    extra.write_text('unlisted own text\n')
    added = run_verify(control, ca)
    extra.unlink()
    if added.returncode == 0 or 'membership mismatch' not in added.stderr:
        raise RuntimeError('membership control failed')
    results.append({'control': 'extra copied-selection member', 'expected': 'REJECT',
                    'returncode': added.returncode, 'output': added.stderr.strip()})
    wrong = dict(ca)
    wrong['REPORT.md'] = '0'*64
    bad_anchor = run_verify(control, wrong)
    if bad_anchor.returncode == 0 or 'detached anchor mismatch' not in bad_anchor.stderr:
        raise RuntimeError('explicit-anchor control failed')
    results.append({'control': 'incorrect explicit REPORT anchor', 'expected': 'REJECT',
                    'returncode': bad_anchor.returncode, 'output': bad_anchor.stderr.strip()})
    write_json(ROOT/'controls/results.json', {'controls': results, 'mathematical_gate': False,
                                             'copied_fixture_restored': True})
    write_json(control/'ANCHORS.json', ca)
    manifest = make_manifest(ROOT, ['packet'], ['FINAL.md', 'verify_packet.py', 'seal_once.py'])
    write_json(ROOT/'MANIFEST.json', manifest)
    final_hash = digest(ROOT/'FINAL.md')
    manifest_hash = digest(ROOT/'MANIFEST.json')
    total = sum(e['bytes'] for e in manifest['files'])
    report = f'''# R162z outside-selection artifact report\n\nDisposition: PREFREEZE / no nominee. No mathematical gate or campaign count is assigned.\n\nThe fresh exact selection is every regular file under packet/ plus FINAL.md, verify_packet.py and seal_once.py: {len(manifest['files'])} files, {total} bytes. No inherited manifest was used. All protected bodies and named metadata are inside packet/private/. This report is outside the manifest selection and is separately anchored. ANCHORS.json and the tiny copied own-text controls are also outside the selection.\n\nFINAL SHA256: {final_hash}\n\nMANIFEST SHA256: {manifest_hash}\n\nTiny copied controls: baseline passed; changed copied bytes rejected; an extra copied-selection member rejected; an incorrect explicitly supplied REPORT anchor rejected. The copied fixture was restored. These controls copied own prose only and used a fresh two-file manifest, not the research manifest over fewer files. Originals were unchanged.\n\nverify_packet.py reads explicit detached FINAL/MANIFEST/REPORT hashes, verifies all selected bytes and exact membership, and performs no writes. Its main invocation is run after computing this report's detached anchor. Artifact integrity does not assess the mathematics.\n\nThe full all-n two-sided spherical diagnostic remains unchanged. The upper same-configuration heat/field construction is unpaid; auxiliary curved lower and cardinality payments are retained privately. Source/primary/history limits and false admissions are disclosed in packet/private/READING-LIMITS.md. Parent alone commissions any later reviews or adopts gates/counts.\n'''
    (ROOT/'REPORT.md').write_text(report)
    main_anchors = anchors(ROOT)
    write_json(ROOT/'ANCHORS.json', main_anchors)
    verification = run_verify(ROOT, main_anchors)
    if verification.returncode:
        raise RuntimeError('main artifact verification failed: '+verification.stderr)
    print(verification.stdout.strip())
    print(json.dumps(main_anchors, indent=2))


if __name__ == '__main__':
    main()
